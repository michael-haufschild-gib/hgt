import GaloisForLFunctions.HTGeometry.ModularFundamentalDomainMeasure
import GaloisForLFunctions.HTGeometry.HolomorphicPoincareSeriesCuspForm

/-!
# Unfolding the modular fundamental domain along the translations

Let `𝒟` be the modular fundamental domain and `H = ⟨T⟩ ≤ PSL₂(ℤ)` the translations.  A system of
representatives of the right cosets `H\PSL₂(ℤ)` is given by the coprime bottom rows `(c, d)` with
`c > 0`, together with `(0, 1)`; for each such row `M_{c,d}` is a matrix with that bottom row.
Hence `⋃ M_{c,d} 𝒟` is a fundamental domain for `H`, as is the strip `{0 ≤ Re z < 1}`, and for a
`T`-periodic `φ` integrable on the strip

  `Σ_{(c,d) coprime} ∫_𝒟 φ(M_{c,d} z) dμ = 2 ∫_{strip} φ dμ`,

the factor `2` counting the two rows `±(c, d)` lying over each coset.

The first section proves the general fact: if `s` is a fundamental domain for `G` and
`R : ι → G` is a system of representatives for the right cosets of a subgroup `H`, so that every
`g` is uniquely `h * R i`, then `⋃ i, R i • s` is a fundamental domain for `H`.
-/

open UpperHalfPlane MeasureTheory ModularGroup Set EisensteinSeries
open scoped MatrixGroups Pointwise

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Fundamental domains for a subgroup from coset representatives -/

section General

variable {G α ι : Type*} [Group G] [MulAction G α] [MeasurableSpace α] {μ : Measure α}
  [MeasurableConstSMul G α] [SMulInvariantMeasure G α μ] [Countable G]

/-- If `s` is a fundamental domain for `G` and every `g ∈ G` is uniquely `h * R i` with `h ∈ H`,
then `⋃ i, R i • s` is a fundamental domain for `H`. -/
theorem isFundamentalDomain_iUnion_smul_of_cosetReps {s : Set α}
    (hs : IsFundamentalDomain G s μ) (H : Subgroup G) (R : ι → G)
    (hsurj : ∀ g : G, ∃ (h : H) (i : ι), (h : G) * R i = g)
    (huniq : ∀ (h h' : H) (i i' : ι), (h : G) * R i = (h' : G) * R i' → h = h' ∧ i = i') :
    IsFundamentalDomain H (⋃ i, R i • s) μ := by
  haveI : Countable ι :=
    Function.Injective.countable (f := R) fun i i' hii' => (huniq 1 1 i i' (by rw [hii'])).2
  refine ⟨NullMeasurableSet.iUnion fun i => hs.nullMeasurableSet_smul (R i), ?_, ?_⟩
  · filter_upwards [hs.ae_covers] with x hx
    obtain ⟨g, hg⟩ := hx
    obtain ⟨h, i, hhi⟩ := hsurj g⁻¹
    refine ⟨h⁻¹, mem_iUnion.mpr ⟨i, mem_smul_set.mpr ⟨g • x, hg, ?_⟩⟩⟩
    rw [smul_smul, Subgroup.smul_def, Subgroup.coe_inv]
    congr 1
    calc R i * g = (h : G)⁻¹ * ((h : G) * R i) * g := by group
      _ = (h : G)⁻¹ := by rw [hhi]; group
  · intro h h' hne
    show μ ((h • ⋃ i, R i • s) ∩ (h' • ⋃ i, R i • s)) = 0
    simp_rw [smul_set_iUnion, iUnion_inter_iUnion]
    refine measure_iUnion_null fun i => measure_iUnion_null fun i' => ?_
    rw [Subgroup.smul_def, Subgroup.smul_def, smul_smul, smul_smul]
    exact hs.aedisjoint fun heq => hne (huniq h h' i i' heq).1

end General

/-! ## The translation subgroup and the strip -/

/-- The image of `T` in `PSL2Z`. -/
abbrev psl2zT : PSL2Z := QuotientGroup.mk ModularGroup.T

/-- The subgroup of translations in `PSL2Z`. -/
abbrev translationSubgroup : Subgroup PSL2Z := Subgroup.zpowers psl2zT

theorem psl2zT_zpow_smul (n : ℤ) (z : ℍ) : (psl2zT ^ n) • z = ModularGroup.T ^ n • z := by
  rw [← QuotientGroup.mk_zpow, PSL2Z_mk_smul]

instance : MeasurableConstSMul translationSubgroup ℍ :=
  ⟨fun h => measurable_const_smul (h : PSL2Z)⟩

instance : SMulInvariantMeasure translationSubgroup ℍ volume :=
  ⟨fun h _ hs => SMulInvariantMeasure.measure_preimage_smul (h : PSL2Z) hs⟩

/-- Every translation acts as some `T ^ n`. -/
theorem translationSubgroup_smul_eq (h : translationSubgroup) (z : ℍ) :
    ∃ n : ℤ, h • z = ModularGroup.T ^ n • z := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h.2
  exact ⟨n, by rw [Subgroup.smul_def, ← hn, psl2zT_zpow_smul]⟩

/-- The strip `0 ≤ Re z < 1`. -/
def modularStrip : Set ℍ := {z | 0 ≤ z.re ∧ z.re < 1}

theorem measurableSet_modularStrip : MeasurableSet modularStrip :=
  measurableSet_Ico.preimage continuous_re.measurable

/-- **The strip is a fundamental domain** for the translations. -/
theorem isFundamentalDomain_modularStrip :
    IsFundamentalDomain translationSubgroup modularStrip volume where
  nullMeasurableSet := measurableSet_modularStrip.nullMeasurableSet
  ae_covers := Filter.Eventually.of_forall fun z => by
    refine ⟨⟨psl2zT ^ (-⌊z.re⌋), Subgroup.zpow_mem_zpowers _ _⟩, ?_⟩
    show (psl2zT ^ (-⌊z.re⌋)) • z ∈ modularStrip
    rw [psl2zT_zpow_smul]
    simp only [modularStrip, mem_setOf_eq, re_T_zpow_smul]
    have h0 := Int.fract_nonneg z.re
    have h1 := Int.fract_lt_one z.re
    rw [← Int.self_sub_floor] at h0 h1
    push_cast
    constructor <;> linarith
  aedisjoint := by
    intro a b hab
    show volume (a • modularStrip ∩ b • modularStrip) = 0
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp b.2
    have : a • modularStrip ∩ b • modularStrip = ∅ := by
      ext z
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      rintro ⟨w, hw, rfl⟩ ⟨w', hw', heq⟩
      have h1 : (a • w).re = w.re + n := by
        rw [Subgroup.smul_def, ← hn, psl2zT_zpow_smul, re_T_zpow_smul]
      have h2 : (b • w').re = w'.re + m := by
        rw [Subgroup.smul_def, ← hm, psl2zT_zpow_smul, re_T_zpow_smul]
      have heq' : b • w' = a • w := heq
      have key : w.re + n = w'.re + m := by rw [← h1, ← h2, heq']
      have hw1 : 0 ≤ w.re ∧ w.re < 1 := hw
      have hw2 : 0 ≤ w'.re ∧ w'.re < 1 := hw'
      have hnm : n = m := by
        have h3 : (n : ℝ) < m + 1 := by linarith [hw1.1, hw1.2, hw2.1, hw2.2, key]
        have h4 : (m : ℝ) < n + 1 := by linarith [hw1.1, hw1.2, hw2.1, hw2.2, key]
        have h3' : n < m + 1 := by exact_mod_cast h3
        have h4' : m < n + 1 := by exact_mod_cast h4
        omega
      exact hab (Subtype.ext (by rw [← hn, ← hm, hnm]))
    rw [this, measure_empty]

/-! ## Coset representatives: coprime bottom rows with `c > 0`, or `(0, 1)` -/

/-- One representative of each pair `±(c, d)` of coprime rows: `c > 0`, or `(c, d) = (0, 1)`. -/
def gammaSetHalf : Set (gammaSet 1 1 0) := {v | 0 < v.1 0 ∨ (v.1 0 = 0 ∧ v.1 1 = 1)}

/-- Negation on coprime pairs. -/
def gammaSetNeg (v : gammaSet 1 1 0) : gammaSet 1 1 0 :=
  ⟨-v.1, by
    rw [gammaSet_one_mem_iff]
    have := (gammaSet_one_mem_iff 1 v.1).mp v.2
    simpa [Int.neg_gcd, Int.gcd_neg] using this⟩

@[simp] theorem gammaSetNeg_val (v : gammaSet 1 1 0) : (gammaSetNeg v).1 = -v.1 := rfl

theorem gammaSetNeg_gammaSetNeg (v : gammaSet 1 1 0) : gammaSetNeg (gammaSetNeg v) = v :=
  Subtype.ext (neg_neg _)

theorem gammaSetNeg_mem_gammaSetHalf_iff (v : gammaSet 1 1 0) :
    gammaSetNeg v ∈ gammaSetHalf ↔ v ∉ gammaSetHalf := by
  simp only [gammaSetHalf, mem_setOf_eq, gammaSetNeg_val, Pi.neg_apply, neg_eq_zero, neg_pos]
  rcases lt_trichotomy (v.1 0) 0 with h | h | h
  · simp [h, h.ne, h.le]
  · rcases gammaSet_snd_eq_of_fst_eq_zero v h with h1 | h1 <;> simp [h, h1]
  · simp [h, h.ne', h.le]

/-- Negation exchanges `gammaSetHalf` with its complement. -/
def gammaSetHalfNegEquiv : gammaSetHalf ≃ (gammaSetHalfᶜ : Set (gammaSet 1 1 0)) where
  toFun v := ⟨gammaSetNeg v.1, (gammaSetNeg_mem_gammaSetHalf_iff (gammaSetNeg v.1)).mp
    (by rw [gammaSetNeg_gammaSetNeg]; exact v.2)⟩
  invFun w := ⟨gammaSetNeg w.1, (gammaSetNeg_mem_gammaSetHalf_iff w.1).mpr w.2⟩
  left_inv v := Subtype.ext (gammaSetNeg_gammaSetNeg v.1)
  right_inv w := Subtype.ext (gammaSetNeg_gammaSetNeg w.1)

theorem eq_of_mem_gammaSetHalf_of_val_eq_neg {v w : gammaSet 1 1 0} (hv : v ∈ gammaSetHalf)
    (hw : w ∈ gammaSetHalf) (h : w.1 = -v.1) : False := by
  simp only [gammaSetHalf, mem_setOf_eq] at hv hw
  rw [h] at hw
  simp only [Pi.neg_apply, neg_pos, neg_eq_zero] at hw
  omega

/-! ## Matrices with a prescribed bottom row differ by translations -/

theorem T_zpow_mul_apply_one (n : ℤ) (B : SL(2, ℤ)) (j : Fin 2) :
    (ModularGroup.T ^ n * B) 1 j = B 1 j := by
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_T_zpow]
  fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem T_zpow_mul_apply_zero (n : ℤ) (B : SL(2, ℤ)) (j : Fin 2) :
    (ModularGroup.T ^ n * B) 0 j = B 0 j + n * B 1 j := by
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_T_zpow]
  fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Two matrices with the same bottom row differ by a power of `T`. -/
theorem exists_eq_T_zpow_mul_of_bottomRow_eq (A B : SL(2, ℤ)) (h0 : A 1 0 = B 1 0)
    (h1 : A 1 1 = B 1 1) : ∃ n : ℤ, A = ModularGroup.T ^ n * B := by
  obtain ⟨n, hn0, hn1⟩ := exists_int_top_row_of_bottomRow_eq A B h0 h1
  refine ⟨n, Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_⟩
  fin_cases i <;> fin_cases j <;>
    simp [T_zpow_mul_apply_zero, T_zpow_mul_apply_one, hn0, hn1, h0, h1]

theorem twoI_mem_fdo : (⟨2 * Complex.I, by simp⟩ : ℍ) ∈ fdo := by
  constructor
  · norm_num [Complex.normSq_apply]
  · norm_num

/-- The kernel of the action is exactly `{±1}`. -/
theorem mem_modularActionKernel_iff (g : SL(2, ℤ)) :
    g ∈ modularActionKernel ↔ g = 1 ∨ g = -1 := by
  constructor
  · intro hg
    have hz : g • (⟨2 * Complex.I, by simp⟩ : ℍ) = ⟨2 * Complex.I, by simp⟩ := by
      rw [MonoidHom.mem_ker, MulAction.toPermHom_apply] at hg
      have := congrArg (fun σ : Equiv.Perm ℍ => σ ⟨2 * Complex.I, by simp⟩) hg
      simpa [MulAction.toPerm_apply] using this
    exact eq_one_or_neg_one_of_mem_fdo_mem_fdo twoI_mem_fdo (by rw [hz]; exact twoI_mem_fdo)
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact neg_one_mem_modularActionKernel

theorem PSL2Z_mk_eq_iff (a b : SL(2, ℤ)) :
    (QuotientGroup.mk a : PSL2Z) = QuotientGroup.mk b ↔ b = a ∨ b = -a := by
  rw [QuotientGroup.eq, mem_modularActionKernel_iff, inv_mul_eq_one]
  constructor
  · rintro (h | h)
    · exact Or.inl h.symm
    · right
      have := congrArg (a * ·) h
      simpa using this
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · right
      simp

theorem PSL2Z_mk_neg (a : SL(2, ℤ)) : (QuotientGroup.mk (-a) : PSL2Z) = QuotientGroup.mk a :=
  (PSL2Z_mk_eq_iff _ _).mpr (Or.inr (neg_neg a).symm)

/-- The coprime pair formed by the bottom row of a matrix. -/
def bottomRowPair (A : SL(2, ℤ)) : gammaSet 1 1 0 :=
  ⟨![A 1 0, A 1 1], by
    rw [gammaSet_one_mem_iff]
    simpa using Int.isCoprime_iff_gcd_eq_one.mp (bottom_row_coprime A)⟩

@[simp] theorem bottomRowPair_val_zero (A : SL(2, ℤ)) : (bottomRowPair A).1 0 = A 1 0 := rfl

@[simp] theorem bottomRowPair_val_one (A : SL(2, ℤ)) : (bottomRowPair A).1 1 = A 1 1 := rfl

theorem exists_eq_T_zpow_mul_gammaSetMatrix (A : SL(2, ℤ)) :
    ∃ n : ℤ, A = ModularGroup.T ^ n * gammaSetMatrix (bottomRowPair A) :=
  exists_eq_T_zpow_mul_of_bottomRow_eq A _ (by simp) (by simp)

theorem bottomRowPair_mem_gammaSetHalf (A : SL(2, ℤ))
    (h : 0 < A 1 0 ∨ (A 1 0 = 0 ∧ A 1 1 = 1)) : bottomRowPair A ∈ gammaSetHalf := by
  simpa [gammaSetHalf] using h

/-- The representative in `PSL2Z` attached to a half-row. -/
def halfRep (v : gammaSetHalf) : PSL2Z := QuotientGroup.mk (gammaSetMatrix v.1)

/-- Every element of `PSL2Z` is a translation times a representative. -/
theorem exists_translation_mul_halfRep (g : PSL2Z) :
    ∃ (h : translationSubgroup) (v : gammaSetHalf), (h : PSL2Z) * halfRep v = g := by
  induction g using QuotientGroup.induction_on with
  | H A =>
  have key : ∀ B : SL(2, ℤ), (0 < B 1 0 ∨ (B 1 0 = 0 ∧ B 1 1 = 1)) →
      ∃ (h : translationSubgroup) (v : gammaSetHalf),
        (h : PSL2Z) * halfRep v = QuotientGroup.mk B := by
    intro B hB
    obtain ⟨n, hn⟩ := exists_eq_T_zpow_mul_gammaSetMatrix B
    refine ⟨⟨psl2zT ^ n, Subgroup.zpow_mem_zpowers _ _⟩,
      ⟨bottomRowPair B, bottomRowPair_mem_gammaSetHalf B hB⟩, ?_⟩
    show psl2zT ^ n * QuotientGroup.mk (gammaSetMatrix (bottomRowPair B)) = QuotientGroup.mk B
    rw [← QuotientGroup.mk_zpow, ← QuotientGroup.mk_mul, ← hn]
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    have := A.det_coe
    rwa [Matrix.det_fin_two] at this
  rcases lt_trichotomy 0 (A 1 0) with hc | hc | hc
  · exact key A (Or.inl hc)
  · have hd : A 1 1 = 1 ∨ A 1 1 = -1 := by
      rw [← hc, mul_zero, sub_zero] at hdet
      exact Int.eq_one_or_neg_one_of_mul_eq_one (by rw [mul_comm]; exact hdet)
    rcases hd with hd | hd
    · exact key A (Or.inr ⟨hc.symm, hd⟩)
    · obtain ⟨h, v, hv⟩ := key (-A) (Or.inr (by simp [← hc, hd]))
      exact ⟨h, v, by rw [hv, PSL2Z_mk_neg]⟩
  · obtain ⟨h, v, hv⟩ := key (-A) (Or.inl (by simpa using hc))
    exact ⟨h, v, by rw [hv, PSL2Z_mk_neg]⟩

theorem bottomRow_eq_of_T_zpow_mul_eq {v w : gammaSet 1 1 0} {n m : ℤ}
    (h : ModularGroup.T ^ m * gammaSetMatrix w = ModularGroup.T ^ n * gammaSetMatrix v) :
    w.1 = v.1 := by
  have h0 := congrArg (fun M : SL(2, ℤ) => (M : Matrix (Fin 2) (Fin 2) ℤ) 1 0) h
  have h1 := congrArg (fun M : SL(2, ℤ) => (M : Matrix (Fin 2) (Fin 2) ℤ) 1 1) h
  simp only [T_zpow_mul_apply_one, gammaSetMatrix_apply_one_zero,
    gammaSetMatrix_apply_one_one] at h0 h1
  funext j
  fin_cases j
  · exact h0
  · exact h1

theorem bottomRow_eq_neg_of_T_zpow_mul_eq_neg {v w : gammaSet 1 1 0} {n m : ℤ}
    (h : ModularGroup.T ^ m * gammaSetMatrix w = -(ModularGroup.T ^ n * gammaSetMatrix v)) :
    w.1 = -v.1 := by
  have h0 := congrArg (fun M : SL(2, ℤ) => (M : Matrix (Fin 2) (Fin 2) ℤ) 1 0) h
  have h1 := congrArg (fun M : SL(2, ℤ) => (M : Matrix (Fin 2) (Fin 2) ℤ) 1 1) h
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, T_zpow_mul_apply_one,
    gammaSetMatrix_apply_one_zero, gammaSetMatrix_apply_one_one] at h0 h1
  funext j
  fin_cases j
  · exact h0
  · exact h1

theorem T_zpow_injective {n m : ℤ} (h : ModularGroup.T ^ n = ModularGroup.T ^ m) : n = m := by
  have := congrArg (fun M : SL(2, ℤ) => (M : Matrix (Fin 2) (Fin 2) ℤ) 0 1) h
  simpa [coe_T_zpow] using this

/-- The decomposition `g = h * halfRep v` is unique. -/
theorem translation_mul_halfRep_injective (h h' : translationSubgroup) (v v' : gammaSetHalf)
    (heq : (h : PSL2Z) * halfRep v = (h' : PSL2Z) * halfRep v') : h = h' ∧ v = v' := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h.2
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h'.2
  have heq' : (QuotientGroup.mk (ModularGroup.T ^ n * gammaSetMatrix v.1) : PSL2Z)
      = QuotientGroup.mk (ModularGroup.T ^ m * gammaSetMatrix v'.1) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_zpow, QuotientGroup.mk_zpow,
      hn, hm]
    exact heq
  rcases (PSL2Z_mk_eq_iff _ _).mp heq' with h1 | h1
  · have hvv : v = v' := Subtype.ext (Subtype.ext (bottomRow_eq_of_T_zpow_mul_eq h1).symm)
    subst hvv
    have hnm : m = n := T_zpow_injective (mul_right_cancel h1)
    exact ⟨Subtype.ext (by rw [← hn, ← hm, hnm]), rfl⟩
  · exact (eq_of_mem_gammaSetHalf_of_val_eq_neg v.2 v'.2
      (bottomRow_eq_neg_of_T_zpow_mul_eq_neg h1)).elim

/-- **The union of the translates `M_{c,d} 𝒟` over the representatives is a fundamental domain
for the translations.** -/
theorem isFundamentalDomain_iUnion_halfRep_smul_fd :
    IsFundamentalDomain translationSubgroup (⋃ v : gammaSetHalf, halfRep v • fd) volume :=
  isFundamentalDomain_iUnion_smul_of_cosetReps isFundamentalDomain_fd translationSubgroup halfRep
    exists_translation_mul_halfRep translation_mul_halfRep_injective

/-! ## The unfolding identity -/

theorem halfRep_smul_fd (v : gammaSetHalf) : halfRep v • fd = gammaSetMatrix v.1 • fd :=
  PSL2Z_mk_smul_set _ _

theorem setIntegral_smul_fd (g : SL(2, ℤ)) (φ : ℍ → ℂ) :
    ∫ z in g • fd, φ z = ∫ z in fd, φ (g • z) := by
  rw [← Set.image_smul]
  exact (measurePreserving_smul g volume).setIntegral_image_emb (measurableEmbedding_const_smul g)
    φ fd

theorem translationSubgroup_invariant_of_periodic {φ : ℍ → ℂ}
    (hφ : ∀ (n : ℤ) (z : ℍ), φ (ModularGroup.T ^ n • z) = φ z) (h : translationSubgroup)
    (z : ℍ) : φ (h • z) = φ z := by
  obtain ⟨n, hn⟩ := translationSubgroup_smul_eq h z
  rw [hn, hφ]

/-- The matrices attached to `±(c, d)` act the same way up to a translation. -/
theorem gammaSetMatrix_gammaSetNeg_smul (v : gammaSet 1 1 0) (z : ℍ) :
    ∃ n : ℤ, gammaSetMatrix (gammaSetNeg v) • z = ModularGroup.T ^ n • (gammaSetMatrix v • z) := by
  obtain ⟨n, hn⟩ := exists_eq_T_zpow_mul_of_bottomRow_eq (gammaSetMatrix (gammaSetNeg v))
    (-gammaSetMatrix v) (by simp) (by simp)
  exact ⟨n, by rw [hn, mul_smul, SL_neg_smul]⟩

/-- The integral of `φ ∘ M_{c,d}` over `𝒟`. -/
def fdUnfoldTerm (φ : ℍ → ℂ) (v : gammaSet 1 1 0) : ℂ := ∫ z in fd, φ (gammaSetMatrix v • z)

theorem fdUnfoldTerm_gammaSetNeg {φ : ℍ → ℂ}
    (hφ : ∀ (n : ℤ) (z : ℍ), φ (ModularGroup.T ^ n • z) = φ z) (v : gammaSet 1 1 0) :
    fdUnfoldTerm φ (gammaSetNeg v) = fdUnfoldTerm φ v := by
  unfold fdUnfoldTerm
  congr 1
  funext z
  obtain ⟨n, hn⟩ := gammaSetMatrix_gammaSetNeg_smul v z
  rw [hn, hφ]

theorem setIntegral_halfRep_smul_fd (φ : ℍ → ℂ) (v : gammaSetHalf) :
    ∫ z in halfRep v • fd, φ z = fdUnfoldTerm φ v.1 := by
  rw [halfRep_smul_fd, setIntegral_smul_fd]
  rfl

theorem integrableOn_iUnion_halfRep_smul_fd {φ : ℍ → ℂ}
    (hφ : ∀ (n : ℤ) (z : ℍ), φ (ModularGroup.T ^ n • z) = φ z)
    (hint : IntegrableOn φ modularStrip volume) :
    IntegrableOn φ (⋃ v : gammaSetHalf, halfRep v • fd) volume :=
  (isFundamentalDomain_modularStrip.integrableOn_iff isFundamentalDomain_iUnion_halfRep_smul_fd
    (translationSubgroup_invariant_of_periodic hφ)).mp hint

theorem hasSum_fdUnfoldTerm_half {φ : ℍ → ℂ}
    (hφ : ∀ (n : ℤ) (z : ℍ), φ (ModularGroup.T ^ n • z) = φ z)
    (hint : IntegrableOn φ modularStrip volume) :
    HasSum (fun v : gammaSetHalf => fdUnfoldTerm φ v.1)
      (∫ z in ⋃ v : gammaSetHalf, halfRep v • fd, φ z) := by
  have hsum : HasSum (fun v : gammaSetHalf => ∫ z in halfRep v • fd, φ z)
      (∫ z in ⋃ v : gammaSetHalf, halfRep v • fd, φ z) :=
    hasSum_integral_iUnion_ae (fun v => isFundamentalDomain_fd.nullMeasurableSet_smul (halfRep v))
      (fun v w hvw => isFundamentalDomain_fd.aedisjoint fun heq =>
        hvw (translation_mul_halfRep_injective 1 1 v w (by simpa using heq)).2)
      (integrableOn_iUnion_halfRep_smul_fd hφ hint)
  have : (fun v : gammaSetHalf => ∫ z in halfRep v • fd, φ z)
      = fun v => fdUnfoldTerm φ v.1 := funext fun v => setIntegral_halfRep_smul_fd φ v
  rw [this] at hsum
  exact hsum

theorem summable_fdUnfoldTerm {φ : ℍ → ℂ}
    (hφ : ∀ (n : ℤ) (z : ℍ), φ (ModularGroup.T ^ n • z) = φ z)
    (hint : IntegrableOn φ modularStrip volume) : Summable (fdUnfoldTerm φ) := by
  have hsumHalf : Summable (fdUnfoldTerm φ ∘ Subtype.val : gammaSetHalf → ℂ) :=
    (hasSum_fdUnfoldTerm_half hφ hint).summable
  have hsumCompl :
      Summable (fdUnfoldTerm φ ∘ Subtype.val : (gammaSetHalfᶜ : Set (gammaSet 1 1 0)) → ℂ) := by
    rw [← gammaSetHalfNegEquiv.summable_iff]
    refine hsumHalf.congr fun v => ?_
    show fdUnfoldTerm φ v.1 = fdUnfoldTerm φ (gammaSetNeg v.1)
    exact (fdUnfoldTerm_gammaSetNeg hφ v.1).symm
  exact Summable.add_compl hsumHalf hsumCompl

theorem tsum_fdUnfoldTerm_eq_two_mul_tsum_half {φ : ℍ → ℂ}
    (hφ : ∀ (n : ℤ) (z : ℍ), φ (ModularGroup.T ^ n • z) = φ z)
    (hint : IntegrableOn φ modularStrip volume) :
    ∑' v, fdUnfoldTerm φ v = 2 * ∑' v : gammaSetHalf, fdUnfoldTerm φ v.1 := by
  have hS := summable_fdUnfoldTerm hφ hint
  have h3 : ∑' x : (gammaSetHalfᶜ : Set (gammaSet 1 1 0)), fdUnfoldTerm φ x.1
      = ∑' v : gammaSetHalf, fdUnfoldTerm φ v.1 := by
    rw [← gammaSetHalfNegEquiv.tsum_eq]
    exact tsum_congr fun v => fdUnfoldTerm_gammaSetNeg hφ v.1
  rw [← hS.tsum_subtype_add_tsum_subtype_compl gammaSetHalf, h3, two_mul]

/-- **Unfolding.** For `T`-periodic `φ` integrable on the strip,
`Σ_{(c,d) coprime} ∫_𝒟 φ(M_{c,d} z) = 2 ∫_{0 ≤ Re z < 1} φ`. -/
theorem tsum_setIntegral_fd_eq_two_mul_setIntegral_modularStrip (φ : ℍ → ℂ)
    (hφ : ∀ (n : ℤ) (z : ℍ), φ (ModularGroup.T ^ n • z) = φ z)
    (hint : IntegrableOn φ modularStrip volume) :
    ∑' v : gammaSet 1 1 0, ∫ z in fd, φ (gammaSetMatrix v • z)
      = 2 * ∫ z in modularStrip, φ z := by
  show ∑' v : gammaSet 1 1 0, fdUnfoldTerm φ v = 2 * ∫ z in modularStrip, φ z
  rw [tsum_fdUnfoldTerm_eq_two_mul_tsum_half hφ hint, (hasSum_fdUnfoldTerm_half hφ hint).tsum_eq,
    isFundamentalDomain_modularStrip.setIntegral_eq isFundamentalDomain_iUnion_halfRep_smul_fd
      (translationSubgroup_invariant_of_periodic hφ)]

/-! ## Integrability on translates of `𝒟` -/

theorem integrableOn_smul_set_iff (g : SL(2, ℤ)) (φ : ℍ → ℂ) (s : Set ℍ) :
    IntegrableOn φ (g • s) volume ↔ IntegrableOn (fun z => φ (g • z)) s volume := by
  rw [← Set.image_smul]
  exact (measurePreserving_smul g volume).integrableOn_image (measurableEmbedding_const_smul g)

/-- A `T`-periodic function integrable on the strip is integrable on every translate `g𝒟`. -/
theorem integrableOn_smul_fd_of_periodic {φ : ℍ → ℂ}
    (hφ : ∀ (n : ℤ) (z : ℍ), φ (ModularGroup.T ^ n • z) = φ z)
    (hint : IntegrableOn φ modularStrip volume) (g : SL(2, ℤ)) :
    IntegrableOn φ (g • fd) volume := by
  obtain ⟨h, v, hv⟩ := exists_translation_mul_halfRep (QuotientGroup.mk g)
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h.2
  have hset : g • fd = ModularGroup.T ^ n • (gammaSetMatrix v.1 • fd) := by
    rw [← PSL2Z_mk_smul_set, ← hv, mul_smul, ← hn, ← QuotientGroup.mk_zpow, PSL2Z_mk_smul_set,
      halfRep_smul_fd]
  rw [hset, integrableOn_smul_set_iff]
  simp only [hφ]
  exact (integrableOn_iUnion_halfRep_smul_fd hφ hint).mono_set
    (subset_iUnion (fun w : gammaSetHalf => halfRep w • fd) v |>.trans_eq' (halfRep_smul_fd v).symm)

end

end GaloisForLFunctions.HTGeometry
