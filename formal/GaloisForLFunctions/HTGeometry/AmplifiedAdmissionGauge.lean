import GaloisForLFunctions.HTGeometry.ReductionPencilKPositivity

/-!
# The amplified admission gauge

This file builds the two-index admission gauge of amplified generative-response mechanics on top of
the sharp reduction-pencil threshold, and proves the four laws of the card
`amplified-admission-depth-escape-and-reduction-pencil-law`:

* the level gauge `κ_k` and the complete gauge, with `κ_k` nondecreasing in `k`
  and complete positivity of `η + cμ` exactly at `c` above every level gauge;
* data processing: a completely positive pre/post comparison cannot create an amplified
  obstruction;
* the exact reduction-pencil profile `κ_k(η_n | T_n) = min k n`, complete gauge `n`;
* the cofinal migrating-depth theorem and the false-promotion theorem.
-/

open Matrix
open scoped ComplexOrder Kronecker
open HTGeometry.ConstraintRelativity

namespace GaloisForLFunctions.HTGeometry

/-! ## Amplification of a matrix map -/

section Amplification

variable {σ τ υ : Type*} [Fintype σ] [Fintype τ] [Fintype υ]

/-- Amplification of a map of matrices by an ancilla index: `id_α ⊗ Φ`. -/
def ampMatMap (α : Type*) (Φ : Matrix σ σ ℂ → Matrix τ τ ℂ)
    (A : Matrix (α × σ) (α × σ) ℂ) : Matrix (α × τ) (α × τ) ℂ :=
  fun x y => Φ (fun i j => A (x.1, i) (y.1, j)) x.2 y.2

/-- Positivity of one amplification level. -/
def IsLevelPositive (α : Type*) [Fintype α] (Φ : Matrix σ σ ℂ → Matrix τ τ ℂ) : Prop :=
  ∀ A : Matrix (α × σ) (α × σ) ℂ, A.PosSemidef → (ampMatMap α Φ A).PosSemidef

/-- Complete positivity: positivity at every finite amplification depth. -/
def IsCompletelyPositiveMap (Φ : Matrix σ σ ℂ → Matrix τ τ ℂ) : Prop :=
  ∀ k : ℕ, IsLevelPositive (Fin k) Φ

theorem ampMatMap_add (α : Type*) (Φ Ψ : Matrix σ σ ℂ → Matrix τ τ ℂ)
    (A : Matrix (α × σ) (α × σ) ℂ) :
    ampMatMap α (fun X => Φ X + Ψ X) A = ampMatMap α Φ A + ampMatMap α Ψ A := rfl

theorem ampMatMap_smul (α : Type*) (r : ℂ) (Φ : Matrix σ σ ℂ → Matrix τ τ ℂ)
    (A : Matrix (α × σ) (α × σ) ℂ) :
    ampMatMap α (fun X => r • Φ X) A = r • ampMatMap α Φ A := rfl

theorem ampMatMap_comp (α : Type*) (Φ : Matrix σ σ ℂ → Matrix τ τ ℂ)
    (Ψ : Matrix τ τ ℂ → Matrix υ υ ℂ) (A : Matrix (α × σ) (α × σ) ℂ) :
    ampMatMap α (fun X => Ψ (Φ X)) A = ampMatMap α Ψ (ampMatMap α Φ A) := rfl

theorem ampMatMap_submatrix {α α' : Type*} (r : α → α') (Φ : Matrix σ σ ℂ → Matrix τ τ ℂ)
    (A : Matrix (α' × σ) (α' × σ) ℂ) :
    ampMatMap α Φ (A.submatrix (fun z => (r z.1, z.2)) (fun z => (r z.1, z.2)))
      = (ampMatMap α' Φ A).submatrix (fun z => (r z.1, z.2)) (fun z => (r z.1, z.2)) := rfl

/-- **Amplification monotonicity.**  Positivity at a level surjects onto positivity at every
smaller level; this is the card's "restrict to a matrix corner". -/
theorem isLevelPositive_of_surjective {α α' : Type*} [Fintype α] [Fintype α']
    {r : α → α'} (hr : Function.Surjective r) (Φ : Matrix σ σ ℂ → Matrix τ τ ℂ)
    (h : IsLevelPositive α Φ) : IsLevelPositive α' Φ := by
  intro A' hA'
  obtain ⟨g, hg⟩ := hr.hasRightInverse
  have h1 := h _ (hA'.submatrix (fun z : α × σ => (r z.1, z.2)))
  rw [ampMatMap_submatrix] at h1
  have h2 := h1.submatrix (fun w : α' × τ => (g w.1, w.2))
  rw [Matrix.submatrix_submatrix] at h2
  have h3 : ((fun z : α × τ => (r z.1, z.2)) ∘ fun w : α' × τ => (g w.1, w.2))
      = (id : α' × τ → α' × τ) := by
    funext w
    simp [hg w.1]
  rwa [h3, Matrix.submatrix_id_id] at h2

/-- Every matrix over an empty index is positive semidefinite, so level `0` is unconditional. -/
theorem isLevelPositive_fin_zero (Φ : Matrix σ σ ℂ → Matrix τ τ ℂ) :
    IsLevelPositive (Fin 0) Φ := by
  intro A _
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext x y; exact absurd x.1.isLt (by omega)
  · intro x
    have hz : (star x ⬝ᵥ ((ampMatMap (Fin 0) Φ A) *ᵥ x)) = 0 := by
      simp only [dotProduct]
      exact Finset.sum_eq_zero fun z _ => absurd z.1.isLt (by omega)
    rw [hz]

/-- Positivity descends along amplification depth. -/
theorem isLevelPositive_fin_antitone {k l : ℕ} (hkl : k ≤ l)
    (Φ : Matrix σ σ ℂ → Matrix τ τ ℂ) (h : IsLevelPositive (Fin l) Φ) :
    IsLevelPositive (Fin k) Φ := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact isLevelPositive_fin_zero Φ
  · refine isLevelPositive_of_surjective (r := fun i : Fin l =>
      if hi : (i : ℕ) < k then (⟨i, hi⟩ : Fin k) else ⟨0, hk⟩) ?_ Φ h
    intro j
    refine ⟨⟨j, lt_of_lt_of_le j.2 hkl⟩, ?_⟩
    simp

end Amplification

/-! ## The level gauge -/

section Gauge

variable {σ τ σ' τ' : Type*} [Fintype σ] [Fintype τ] [Fintype σ'] [Fintype τ']

/-- (AGR.1) The set of coefficients admitted at amplification depth `k`. -/
def levelFeasible (k : ℕ) (η μ : Matrix σ σ ℂ →ₗ[ℂ] Matrix τ τ ℂ) : Set ℝ :=
  {c : ℝ | 0 ≤ c ∧ IsLevelPositive (Fin k) (fun X => η X + (c : ℂ) • μ X)}

/-- (AGR.1) The level-`k` intervention gauge. -/
noncomputable def levelGauge (k : ℕ) (η μ : Matrix σ σ ℂ →ₗ[ℂ] Matrix τ τ ℂ) : ℝ :=
  sInf (levelFeasible k η μ)

private theorem matSesq_add_smul {I : Type*} [Fintype I] (M N : Matrix I I ℂ) (r : ℂ)
    (x : I → ℂ) : matSesq (M + r • N) x x = matSesq M x x + r * matSesq N x x := by
  simp only [matSesq, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

variable {η μ : Matrix σ σ ℂ →ₗ[ℂ] Matrix τ τ ℂ}

theorem levelFeasible_nonneg {k : ℕ} {c : ℝ} (hc : c ∈ levelFeasible k η μ) : 0 ≤ c := hc.1

theorem levelFeasible_bddBelow (k : ℕ) (η μ : Matrix σ σ ℂ →ₗ[ℂ] Matrix τ τ ℂ) :
    BddBelow (levelFeasible k η μ) := ⟨0, fun _ hc => hc.1⟩

theorem levelGauge_nonneg (k : ℕ) (η μ : Matrix σ σ ℂ →ₗ[ℂ] Matrix τ τ ℂ)
    (hne : (levelFeasible k η μ).Nonempty) : 0 ≤ levelGauge k η μ :=
  le_csInf hne fun _ hc => hc.1

/-- **The feasible sets shrink with amplification depth.** -/
theorem levelFeasible_antitone {k l : ℕ} (hkl : k ≤ l) :
    levelFeasible l η μ ⊆ levelFeasible k η μ := by
  rintro c ⟨hc0, hc⟩
  exact ⟨hc0, isLevelPositive_fin_antitone hkl _ hc⟩

/-- **The level gauge is nondecreasing (Theorem 1.1, first clause).** -/
theorem levelGauge_mono {k l : ℕ} (hkl : k ≤ l) (hne : (levelFeasible l η μ).Nonempty) :
    levelGauge k η μ ≤ levelGauge l η μ :=
  csInf_le_csInf (levelFeasible_bddBelow k η μ) hne (levelFeasible_antitone hkl)

/-- The feasible set is an upper set when the comparison map is completely positive. -/
theorem levelFeasible_up {k : ℕ} (hμ : IsCompletelyPositiveMap (⇑μ)) {c d : ℝ}
    (hc : c ∈ levelFeasible k η μ) (hcd : c ≤ d) : d ∈ levelFeasible k η μ := by
  refine ⟨le_trans hc.1 hcd, fun A hA => ?_⟩
  have h1 := hc.2 A hA
  have h2 := hμ k A hA
  have hsplit : ampMatMap (Fin k) (fun X => η X + (d : ℂ) • μ X) A
      = ampMatMap (Fin k) (fun X => η X + (c : ℂ) • μ X) A
        + ((d - c : ℝ) : ℂ) • ampMatMap (Fin k) (⇑μ) A := by
    ext x y
    simp only [ampMatMap, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
      Complex.ofReal_sub]
    ring
  rw [hsplit]
  exact h1.add ((h2.smul (by exact_mod_cast sub_nonneg.mpr hcd)))

/-- **Attainment.**  With a completely positive comparison map, a nonempty feasible set is the
closed ray above its infimum: the level gauge is itself admitted. -/
theorem levelFeasible_eq_Ici {k : ℕ} (hμ : IsCompletelyPositiveMap (⇑μ))
    (hne : (levelFeasible k η μ).Nonempty) :
    levelFeasible k η μ = Set.Ici (levelGauge k η μ) := by
  apply Set.Subset.antisymm
  · exact fun c hc => csInf_le (levelFeasible_bddBelow k η μ) hc
  · intro c hc
    have habove : ∀ ε : ℝ, 0 < ε → (c + ε) ∈ levelFeasible k η μ := by
      intro ε hε
      obtain ⟨c', hc', hlt⟩ := exists_lt_of_csInf_lt hne
        (show levelGauge k η μ < c + ε from lt_of_le_of_lt hc (by linarith))
      exact levelFeasible_up hμ hc' hlt.le
    refine ⟨le_trans (levelGauge_nonneg k η μ hne) hc, fun A hA => ?_⟩
    have hμA := hμ k A hA
    have hsplit : ∀ ε : ℝ, ampMatMap (Fin k) (fun X => η X + ((c + ε : ℝ) : ℂ) • μ X) A
        = ampMatMap (Fin k) (fun X => η X + (c : ℂ) • μ X) A
          + (ε : ℂ) • ampMatMap (Fin k) (⇑μ) A := by
      intro ε
      ext x y
      simp only [ampMatMap, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_add]
      ring
    set M := ampMatMap (Fin k) (fun X => η X + (c : ℂ) • μ X) A with hM
    set N := ampMatMap (Fin k) (⇑μ) A with hN
    have hpos : ∀ ε : ℝ, 0 < ε → (M + (ε : ℂ) • N).PosSemidef := by
      intro ε hε
      have := (habove ε hε).2 A hA
      rwa [hsplit ε] at this
    -- Hermitian: two distinct positive values pin both parts
    have hherm : M.IsHermitian := by
      have h1 := (hpos 1 one_pos).isHermitian
      have hN' : N.IsHermitian := hμA.isHermitian
      have : Mᴴ = M := by
        have e1 : (M + ((1 : ℝ) : ℂ) • N)ᴴ = M + ((1 : ℝ) : ℂ) • N := h1
        rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hN'] at e1
        simpa using e1
      exact this
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm fun x => ?_
    rw [← matSesq_eq_dotProduct]
    have hre : ∀ ε : ℝ, 0 < ε →
        0 ≤ (matSesq M x x).re + ε * (matSesq N x x).re := by
      intro ε hε
      have hp := matSesq_self_re_nonneg (hpos ε hε) x
      rw [matSesq_add_smul] at hp
      simpa [Complex.add_re, Complex.re_ofReal_mul] using hp
    have hM0 : 0 ≤ (matSesq M x x).re := by
      by_contra hlt
      rw [not_le] at hlt
      set a := (matSesq M x x).re with ha
      set b := (matSesq N x x).re with hbdef
      have hb : 0 ≤ b := matSesq_self_re_nonneg hμA x
      rcases eq_or_lt_of_le hb with hb0 | hb0
      · have h1 := hre 1 one_pos
        rw [← hb0] at h1
        simp only [mul_zero, add_zero] at h1
        linarith
      · have hbne : b ≠ 0 := ne_of_gt hb0
        have hεpos : 0 < -a / (2 * b) := div_pos (by linarith) (by linarith)
        have h2 := hre (-a / (2 * b)) hεpos
        have hcalc : (-a / (2 * b)) * b = -a / 2 := by field_simp
        rw [hcalc] at h2
        linarith
    have him : (matSesq M x x).im = 0 := matSesq_self_im hherm x
    exact Complex.le_def.mpr ⟨by simpa using hM0, by simpa using him.symm⟩

/-- **(AGR.3)**  `η + cμ` is completely positive exactly when `c` is at least every level gauge. -/
theorem isCompletelyPositiveMap_iff_forall_levelGauge_le (hμ : IsCompletelyPositiveMap (⇑μ))
    (hne : ∀ k, (levelFeasible k η μ).Nonempty) {c : ℝ} (hc0 : 0 ≤ c) :
    IsCompletelyPositiveMap (fun X => η X + (c : ℂ) • μ X) ↔ ∀ k, levelGauge k η μ ≤ c := by
  constructor
  · intro h k
    exact csInf_le (levelFeasible_bddBelow k η μ) ⟨hc0, h k⟩
  · intro h k
    have hmem : c ∈ levelFeasible k η μ := by
      rw [levelFeasible_eq_Ici hμ (hne k)]; exact h k
    exact hmem.2

/-- **(AGR.4)**  Data processing: a completely positive pre- and post-comparison can only enlarge
the feasible set, so it cannot create an amplified obstruction. -/
theorem levelFeasible_subset_comp (Apre : Matrix σ' σ' ℂ →ₗ[ℂ] Matrix σ σ ℂ)
    (Bpost : Matrix τ τ ℂ →ₗ[ℂ] Matrix τ' τ' ℂ)
    (hA : IsCompletelyPositiveMap (⇑Apre)) (hB : IsCompletelyPositiveMap (⇑Bpost)) (k : ℕ) :
    levelFeasible k η μ
      ⊆ levelFeasible k (Bpost.comp (η.comp Apre)) (Bpost.comp (μ.comp Apre)) := by
  rintro c ⟨hc0, hc⟩
  refine ⟨hc0, fun A hA' => ?_⟩
  have hrw : ampMatMap (Fin k)
      (fun X => (Bpost.comp (η.comp Apre)) X + (c : ℂ) • (Bpost.comp (μ.comp Apre)) X) A
      = ampMatMap (Fin k) (⇑Bpost)
          (ampMatMap (Fin k) (fun Y => η Y + (c : ℂ) • μ Y)
            (ampMatMap (Fin k) (⇑Apre) A)) := by
    rw [← ampMatMap_comp, ← ampMatMap_comp]
    congr 1
    funext X
    simp [map_add, map_smul]
  rw [hrw]
  exact hB k _ (hc _ (hA k A hA'))

/-- **(AGR.4)** in gauge form. -/
theorem levelGauge_comp_le (Apre : Matrix σ' σ' ℂ →ₗ[ℂ] Matrix σ σ ℂ)
    (Bpost : Matrix τ τ ℂ →ₗ[ℂ] Matrix τ' τ' ℂ)
    (hA : IsCompletelyPositiveMap (⇑Apre)) (hB : IsCompletelyPositiveMap (⇑Bpost)) (k : ℕ)
    (hne : (levelFeasible k η μ).Nonempty) :
    levelGauge k (Bpost.comp (η.comp Apre)) (Bpost.comp (μ.comp Apre)) ≤ levelGauge k η μ :=
  csInf_le_csInf (levelFeasible_bddBelow _ _ _) hne (levelFeasible_subset_comp Apre Bpost hA hB k)

/-- (AGR.2) The complete gauge. -/
noncomputable def completeGauge (η μ : Matrix σ σ ℂ →ₗ[ℂ] Matrix τ τ ℂ) : ℝ :=
  sSup (Set.range fun k => levelGauge k η μ)

end Gauge

/-! ## The reduction pencil -/

section Reduction

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- The source intervention `η_n(X) = −X`. -/
def reductionEta : Matrix β β ℂ →ₗ[ℂ] Matrix β β ℂ := -LinearMap.id

/-- The comparison map `T_n(X) = Tr(X)·1`. -/
def reductionTrace : Matrix β β ℂ →ₗ[ℂ] Matrix β β ℂ where
  toFun X := X.trace • (1 : Matrix β β ℂ)
  map_add' X Y := by simp [Matrix.trace_add, add_smul]
  map_smul' r X := by simp [Matrix.trace_smul, smul_smul]

theorem ampMatMap_reduction (α : Type*) [Fintype α] [DecidableEq α] (c : ℝ)
    (A : Matrix (α × β) (α × β) ℂ) :
    ampMatMap α (fun X => reductionEta X + (c : ℂ) • reductionTrace X) A = redPencil c A := by
  ext x y
  simp only [ampMatMap, reductionEta, reductionTrace, LinearMap.neg_apply, LinearMap.id_apply,
    LinearMap.coe_mk, AddHom.coe_mk, Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply,
    smul_eq_mul, redPencil, Matrix.sub_apply, Matrix.kroneckerMap_apply, partialTraceRight,
    Matrix.trace, Matrix.diag_apply, Finset.sum_apply]
  ring

/-- **Theorem 2.1 as a level-positivity statement.** -/
theorem isLevelPositive_reduction_iff {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] [Nonempty β] (c : ℝ) :
    IsLevelPositive α (fun X : Matrix β β ℂ => reductionEta X + (c : ℂ) • reductionTrace X)
      ↔ ((min (Fintype.card α) (Fintype.card β) : ℕ) : ℝ) ≤ c := by
  unfold IsLevelPositive
  simp only [ampMatMap_reduction]
  exact redPencil_posSemidef_forall_iff c

/-- **(AGR.7)**  The exact reduction-pencil level gauge is `min k n`. -/
theorem levelGauge_reduction (n : ℕ) (hn : 0 < n) (k : ℕ) :
    levelGauge k (reductionEta (β := Fin n)) reductionTrace = ((min k n : ℕ) : ℝ) := by
  have hset : levelFeasible k (reductionEta (β := Fin n)) reductionTrace
      = Set.Ici ((min k n : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · ext c
      simp only [levelFeasible, Set.mem_setOf_eq, Set.mem_Ici, Nat.zero_min, Nat.cast_zero]
      exact ⟨fun h => h.1, fun h => ⟨h, isLevelPositive_fin_zero _⟩⟩
    · have hk' : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
      have hn' : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      ext c
      simp only [levelFeasible, Set.mem_setOf_eq, Set.mem_Ici]
      rw [isLevelPositive_reduction_iff, Fintype.card_fin, Fintype.card_fin]
      exact ⟨fun h => h.2, fun h => ⟨le_trans (Nat.cast_nonneg _) h, h⟩⟩
  rw [levelGauge, hset, csInf_Ici]

/-- **(AGR.7)**  The complete gauge of the reduction pencil at aperture `n` is `n`. -/
theorem isGreatest_completeGauge_reduction (n : ℕ) (hn : 0 < n) :
    IsGreatest (Set.range fun k => levelGauge k (reductionEta (β := Fin n)) reductionTrace)
      (n : ℝ) := by
  constructor
  · refine ⟨n, ?_⟩
    dsimp only
    rw [levelGauge_reduction n hn, min_self]
  · rintro x ⟨k, rfl⟩
    dsimp only
    rw [levelGauge_reduction n hn]
    exact_mod_cast min_le_right k n

theorem completeGauge_reduction (n : ℕ) (hn : 0 < n) :
    completeGauge (reductionEta (β := Fin n)) reductionTrace = (n : ℝ) :=
  (isGreatest_completeGauge_reduction n hn).csSup_eq

/-- **(AGR.12)**  Every fixed amplification depth has one aperture-uniform bound, attained. -/
theorem isGreatest_fixed_depth_reduction (k : ℕ) (hk : 0 < k) :
    IsGreatest {x : ℝ | ∃ n : ℕ, 0 < n ∧
        levelGauge k (reductionEta (β := Fin n)) reductionTrace = x} (k : ℝ) := by
  constructor
  · exact ⟨k, hk, by rw [levelGauge_reduction k hk, min_self]⟩
  · rintro x ⟨n, hn, rfl⟩
    rw [levelGauge_reduction n hn]
    exact_mod_cast min_le_left k n

/-- **(AGR.13)**  The complete gauges are cofinally unbounded in the aperture. -/
theorem completeGauge_reduction_not_bddAbove :
    ¬ ∃ C : ℝ, ∀ n : ℕ, 0 < n → completeGauge (reductionEta (β := Fin n)) reductionTrace ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨m, hm⟩ := exists_nat_gt C
  have h := hC (m + 1) (Nat.succ_pos m)
  rw [completeGauge_reduction (m + 1) (Nat.succ_pos m)] at h
  have : (m : ℝ) < ((m : ℝ) + 1) := by linarith
  push_cast at h
  linarith

/-- **(AGR.14)  False-promotion theorem.**  Separate uniform bounds at every fixed amplification
depth do not promote to one uniform complete bound. -/
theorem reduction_false_promotion :
    (∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ, 0 < n →
        levelGauge k (reductionEta (β := Fin n)) reductionTrace ≤ C)
      ∧ ¬ ∃ C : ℝ, ∀ n : ℕ, 0 < n →
        completeGauge (reductionEta (β := Fin n)) reductionTrace ≤ C := by
  refine ⟨fun k => ⟨(k : ℝ), fun n hn => ?_⟩, completeGauge_reduction_not_bddAbove⟩
  rw [levelGauge_reduction n hn]
  exact_mod_cast min_le_left k n

end Reduction

end GaloisForLFunctions.HTGeometry
