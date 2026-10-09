import GaloisForLFunctions.HilbertMetric.HorizontalLamzouriRouteToMultiple

/-!
# Merging a mixed class into one multiple real point

A mixed class is a real point `x` together with a conjugate pair `q` on the same horizontal line;
it enters the packet as the atoms `(1, f_x)`, `(2m_q, g_q)`, `(−2m_q, h_q)`. The *merged* packet
replaces the class by one real point of multiplicity `2m_q + 1` with vector `f_x`. The count is
unchanged, and multiple real points cost nothing in the four-trace bound, so no averaging over
owners is needed.

**Transfer identity** (`four_mass_sub_energy_transfer_eq`). If a packet `P′` arises from `P` by
adding a signed family of atoms `(c_j, a_j)`, i.e. `Σ wt′F(vec′) = Σ wt F(vec) + Σ c_j F(a_j)` for
every `F`, then with `D′` the diagonal form of `P′`,
`4·mass − E = 4·mass′ − E′ − 4Σ c_j‖a_j‖² + 2Σ c_j D′(a_j) − Σ_{j,j′} c_j c_{j′}⟪a_j, a_{j′}⟫²`.

**Merge identity** (`four_mass_sub_energy_merge_eq`, `four_mass_sub_energy_le_merge`). Merging the
classes `q ∈ S`, each with its real point `f_q = f_{mate q}`, gives
`4·mass − E − 2N ≤ 4·mass′ − E′ − 2N′ + Σ_{q∈S} 4m_q(2(‖g_q‖² − ‖h_q‖² − ‖f_q‖²)
  + D′(f_q) + D′(h_q) − D′(g_q))`.
The merged atom `(2m_q + 1, f_q)` lies in `D′`, so the cost of class `q` contains the self term
`4m_q(2m_q + 1)(‖f_q‖⁴ + ⟪f_q, h_q⟫² − ⟪f_q, g_q⟫²)`, which is a gain whenever
`⟪f_q, g_q⟫² ≥ ‖f_q‖⁴ + ⟪f_q, h_q⟫²`.
-/

open scoped RealInnerProductSpace
open Finset Module

noncomputable section

namespace GaloisForLFunctions.HilbertMetric

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace HorizontalPacket

section Transfer

variable {ι₂ ιH ιM ιP : Type*} [Fintype ι₂] [Fintype ιH] [Fintype ιM] [Fintype ιP]
variable {κ₂ κH κM κP : Type*} [Fintype κ₂] [Fintype κH] [Fintype κM] [Fintype κP]
variable (P : HorizontalPacket V ι₂ ιH ιM ιP) (P' : HorizontalPacket V κ₂ κH κM κP)

/-- **Transfer identity for the energy.** -/
theorem energy_transfer {J : Type*} [Fintype J] (c : J → ℝ) (a : J → V)
    (htr : ∀ F : V → ℝ, ∑ k, P'.wt k * F (P'.vec k) =
      ∑ k, P.wt k * F (P.vec k) + ∑ j, c j * F (a j)) :
    P'.energy = P.energy + 2 * ∑ j, c j * P'.diagForm (a j) -
      ∑ j, ∑ j', c j * c j' * ⟪a j, a j'⟫ ^ 2 := by
  set D' := P'.diagForm with hD'
  have hdiag : ∀ ψ, D' ψ = P.diagForm ψ + ∑ j, c j * ⟪a j, ψ⟫ ^ 2 := fun ψ =>
    htr fun v => ⟪v, ψ⟫ ^ 2
  rw [energy_eq_sum_diagForm, htr D']
  have h1 : ∑ k, P.wt k * D' (P.vec k) = P.energy + ∑ j, c j * P.diagForm (a j) := by
    simp only [hdiag, mul_add, Finset.sum_add_distrib, ← energy_eq_sum_diagForm]
    congr 1
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [diagForm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [real_inner_comm]; ring
  have h4 : ∑ j, c j * P.diagForm (a j) =
      ∑ j, c j * D' (a j) - ∑ j, ∑ j', c j * c j' * ⟪a j, a j'⟫ ^ 2 := by
    simp only [hdiag, mul_add, Finset.sum_add_distrib]
    have : ∑ j, c j * ∑ j', c j' * ⟪a j', a j⟫ ^ 2 =
        ∑ j, ∑ j', c j * c j' * ⟪a j, a j'⟫ ^ 2 := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j' _ => ?_
      rw [real_inner_comm]; ring
    rw [this]; ring
  rw [h1, h4]
  ring

/-- **Transfer identity.** -/
theorem four_mass_sub_energy_transfer_eq {J : Type*} [Fintype J] (c : J → ℝ) (a : J → V)
    (htr : ∀ F : V → ℝ, ∑ k, P'.wt k * F (P'.vec k) =
      ∑ k, P.wt k * F (P.vec k) + ∑ j, c j * F (a j)) :
    4 * P.mass - P.energy =
      4 * P'.mass - P'.energy - 4 * ∑ j, c j * ‖a j‖ ^ 2 +
        2 * ∑ j, c j * P'.diagForm (a j) - ∑ j, ∑ j', c j * c j' * ⟪a j, a j'⟫ ^ 2 := by
  have hm : P'.mass = P.mass + ∑ j, c j * ‖a j‖ ^ 2 := htr fun v => ‖v‖ ^ 2
  rw [hm, P.energy_transfer P' c a htr]
  ring

omit [Fintype ι₂] [Fintype ιH] [Fintype ιM] [Fintype ιP] in
/-- The Gram term `Σ c_j c_{j′}⟪a_j, a_{j′}⟫² = ‖Σ c_j a_j⊗a_j‖²` is nonnegative. -/
theorem sum_sum_mul_inner_sq_nonneg [FiniteDimensional ℝ V] {J : Type*} [Fintype J]
    (c : J → ℝ) (a : J → V) : 0 ≤ ∑ j, ∑ j', c j * c j' * ⟪a j, a j'⟫ ^ 2 := by
  obtain ⟨b, ev, hd⟩ := exists_weightedForm_diag c a
  have h := sum_weight_mul_weightedForm_eq c a b ev hd
  have e : ∑ j, ∑ j', c j * c j' * ⟪a j, a j'⟫ ^ 2 = ∑ j, c j * weightedForm c a (a j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [weightedForm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [real_inner_comm]; ring
  rw [e, h]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- The transfer can only gain from the Gram term:
`4·mass − E ≤ 4·mass′ − E′ − 4Σc‖a‖² + 2ΣcD′(a)`. -/
theorem four_mass_sub_energy_le_transfer [FiniteDimensional ℝ V] {J : Type*} [Fintype J]
    (c : J → ℝ) (a : J → V)
    (htr : ∀ F : V → ℝ, ∑ k, P'.wt k * F (P'.vec k) =
      ∑ k, P.wt k * F (P.vec k) + ∑ j, c j * F (a j)) :
    4 * P.mass - P.energy ≤
      4 * P'.mass - P'.energy - 4 * ∑ j, c j * ‖a j‖ ^ 2 +
        2 * ∑ j, c j * P'.diagForm (a j) := by
  rw [P.four_mass_sub_energy_transfer_eq P' c a htr]
  linarith [sum_sum_mul_inner_sq_nonneg c a]

end Transfer

section Merge

variable {ι₂ ιH ιM ιP : Type*} [Fintype ι₂] [Fintype ιH] [Fintype ιM] [Fintype ιP]
  [DecidableEq ιM] [DecidableEq ιP]
variable (P : HorizontalPacket V ι₂ ιH ιM ιP) (S : Finset ιP) (mate : {q // q ∈ S} → ιM)

/-- The packet in which each class `q ∈ S` (the pair `q` and the real point `mate q`) becomes one
real point of multiplicity `2m_q + 1` with vector `f_{mate q}`. -/
def mergeMixed : HorizontalPacket V (ι₂ ⊕ {q // q ∈ S}) ιH
    {x // x ∉ Finset.univ.image mate} {q // q ∉ S} where
  f₂ := Sum.elim P.f₂ fun q => P.fM (mate q)
  m₂ := Sum.elim P.m₂ fun q => 2 * P.mP q + 1
  fH := P.fH
  fM x := P.fM x
  g q := P.g q
  h q := P.h q
  mP q := P.mP q

omit [Fintype ιP] [DecidableEq ιP] in
theorem sum_mate_add_sum_not_mate (hmate : Function.Injective mate) (G : ιM → ℝ) :
    ∑ q : {q // q ∈ S}, G (mate q) + ∑ x : {x // x ∉ Finset.univ.image mate}, G x =
      ∑ x, G x := by
  have h1 : ∑ q : {q // q ∈ S}, G (mate q) =
      ∑ x : {x // x ∈ Finset.univ.image mate}, G x := by
    rw [Finset.sum_coe_sort (Finset.univ.image mate) G, Finset.sum_image fun a _ b _ h => hmate h]
  rw [h1]
  convert Fintype.sum_subtype_add_sum_subtype (fun x => x ∈ Finset.univ.image mate) G

/-- The signed atoms moved by the merge: `+2m f_q`, `+2m h_q`, `−2m g_q`. -/
def mergeWeight : {q // q ∈ S} ⊕ {q // q ∈ S} ⊕ {q // q ∈ S} → ℝ :=
  Sum.elim (fun q => 2 * P.mP q) (Sum.elim (fun q => 2 * P.mP q) fun q => -(2 * P.mP q))

/-- The vectors of the moved atoms. -/
def mergeVec : {q // q ∈ S} ⊕ {q // q ∈ S} ⊕ {q // q ∈ S} → V :=
  Sum.elim (fun q => P.fM (mate q)) (Sum.elim (fun q => P.h q) fun q => P.g q)

theorem merge_sum_wt_mul (hmate : Function.Injective mate) (F : V → ℝ) :
    ∑ k, (P.mergeMixed S mate).wt k * F ((P.mergeMixed S mate).vec k) =
      ∑ k, P.wt k * F (P.vec k) + ∑ j, P.mergeWeight S j * F (P.mergeVec S mate j) := by
  rw [sum_wt_mul, sum_wt_mul]
  have hg := sum_mem_add_sum_not_mem S fun q => 2 * P.mP q * F (P.g q)
  have hh := sum_mem_add_sum_not_mem S fun q => 2 * P.mP q * F (P.h q)
  have hm := sum_mate_add_sum_not_mate S mate hmate fun x => F (P.fM x)
  simp only [mergeMixed, mergeWeight, mergeVec, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr]
  rw [← hg, ← hh, ← hm]
  simp only [add_mul, one_mul, Finset.sum_add_distrib, neg_mul, Finset.sum_neg_distrib]
  ring

theorem merge_count (hmate : Function.Injective mate) :
    (P.mergeMixed S mate).count = P.count := by
  have hm := sum_mate_add_sum_not_mate S mate hmate fun _ => (1 : ℝ)
  have hp := sum_mem_add_sum_not_mem S P.mP
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hm
  simp only [count, mergeMixed, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  rw [← hm, ← hp, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, ← Finset.mul_sum]
  ring

/-- **Merge bound.** -/
theorem four_mass_sub_energy_le_merge [FiniteDimensional ℝ V] (hmate : Function.Injective mate) :
    4 * P.mass - P.energy - 2 * P.count ≤
      4 * (P.mergeMixed S mate).mass - (P.mergeMixed S mate).energy -
          2 * (P.mergeMixed S mate).count +
        ∑ q : {q // q ∈ S}, 4 * P.mP q *
          (2 * (‖P.g q‖ ^ 2 - ‖P.h q‖ ^ 2 - ‖P.fM (mate q)‖ ^ 2) +
            (P.mergeMixed S mate).diagForm (P.fM (mate q)) +
            (P.mergeMixed S mate).diagForm (P.h q) - (P.mergeMixed S mate).diagForm (P.g q)) := by
  have h := P.four_mass_sub_energy_le_transfer (P.mergeMixed S mate) (P.mergeWeight S)
    (P.mergeVec S mate) (P.merge_sum_wt_mul S mate hmate)
  rw [P.merge_count S mate hmate]
  have e1 : ∑ j, P.mergeWeight S j * ‖P.mergeVec S mate j‖ ^ 2 =
      ∑ q : {q // q ∈ S}, 2 * P.mP q *
        (‖P.fM (mate q)‖ ^ 2 + ‖P.h q‖ ^ 2 - ‖P.g q‖ ^ 2) := by
    simp only [mergeWeight, mergeVec, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      neg_mul, Finset.sum_neg_distrib]
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => by ring
  have e2 : ∑ j, P.mergeWeight S j * (P.mergeMixed S mate).diagForm (P.mergeVec S mate j) =
      ∑ q : {q // q ∈ S}, 2 * P.mP q *
        ((P.mergeMixed S mate).diagForm (P.fM (mate q)) +
          (P.mergeMixed S mate).diagForm (P.h q) - (P.mergeMixed S mate).diagForm (P.g q)) := by
    simp only [mergeWeight, mergeVec, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      neg_mul, Finset.sum_neg_distrib]
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [e1, e2] at h
  have e3 : -(4 * ∑ q : {q // q ∈ S}, 2 * P.mP q *
        (‖P.fM (mate q)‖ ^ 2 + ‖P.h q‖ ^ 2 - ‖P.g q‖ ^ 2)) +
      2 * ∑ q : {q // q ∈ S}, 2 * P.mP q *
        ((P.mergeMixed S mate).diagForm (P.fM (mate q)) +
          (P.mergeMixed S mate).diagForm (P.h q) - (P.mergeMixed S mate).diagForm (P.g q)) =
      ∑ q : {q // q ∈ S}, 4 * P.mP q *
        (2 * (‖P.g q‖ ^ 2 - ‖P.h q‖ ^ 2 - ‖P.fM (mate q)‖ ^ 2) +
          (P.mergeMixed S mate).diagForm (P.fM (mate q)) +
          (P.mergeMixed S mate).diagForm (P.h q) - (P.mergeMixed S mate).diagForm (P.g q)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => by ring
  linarith

omit [DecidableEq ιM] [DecidableEq ιP] in
/-- The four-trace bound with every mixed point charged at most `1`:
`4·mass − E − 2N ≤ #H + #M`. -/
theorem four_mass_sub_energy_le_card_add_card [FiniteDimensional ℝ V] (hm₂ : ∀ i, 2 ≤ P.m₂ i)
    (hmP : ∀ q, 1 ≤ P.mP q) (hH : ∀ i, ‖P.fH i‖ ≤ 1) (hMn : ∀ x, ‖P.fM x‖ ≤ 1) :
    4 * P.mass - P.energy - 2 * P.count ≤
      (Fintype.card ιH : ℝ) + (Fintype.card ιM : ℝ) := by
  obtain ⟨e, ev, hd⟩ := exists_weightedForm_diag P.pairWeight P.pairVec
  have hd' : ∀ v, P.pairField v = ∑ j, ev j * ⟪e j, v⟫ ^ 2 := fun v => by
    rw [P.pairField_eq, hd]
  have h := P.spectral_four_mass_bound_positivePart e ev hd' hm₂ hmP
  have hPp : 0 ≤ ∑ x, positivePartForm e ev (P.fM x) :=
    Finset.sum_nonneg fun x _ => positivePartForm_nonneg _ _ _
  have hsl : 0 ≤ max (P.pairTrace - 2 * Fintype.card ιP) 0 ^ 2 / Fintype.card ιP :=
    div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  have hHs : ∑ i, (2 * ‖P.fH i‖ ^ 2 - 1) ≤ (Fintype.card ιH : ℝ) := by
    have : ∀ i, 2 * ‖P.fH i‖ ^ 2 - 1 ≤ 1 := fun i => by
      have := hH i; nlinarith [norm_nonneg (P.fH i)]
    have hs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => this i
    rwa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hs
  have hMs : ∑ x, (2 * ‖P.fM x‖ ^ 2 - 1) ≤ (Fintype.card ιM : ℝ) := by
    have : ∀ x, 2 * ‖P.fM x‖ ^ 2 - 1 ≤ 1 := fun x => by
      have := hMn x; nlinarith [norm_nonneg (P.fM x)]
    have hs := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) => this x
    rwa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hs
  linarith

/-- **Merged count.** Merging the classes of `S` with their real points `mate q`:
`4·mass − E − 2N ≤ #H + #{unmerged mixed points} + Σ_{q∈S} c_q`, where
`c_q = 4m_q(2(‖g_q‖² − ‖h_q‖² − ‖f_q‖²) + D′(f_q) + D′(h_q) − D′(g_q))`. -/
theorem four_mass_sub_energy_le_merge_add_card [FiniteDimensional ℝ V]
    (hmate : Function.Injective mate) (hm₂ : ∀ i, 2 ≤ P.m₂ i) (hmP : ∀ q, 1 ≤ P.mP q)
    (hH : ∀ i, ‖P.fH i‖ ≤ 1) (hMn : ∀ x, ‖P.fM x‖ ≤ 1) :
    4 * P.mass - P.energy - 2 * P.count ≤
      (Fintype.card ιH : ℝ) + (Fintype.card {x // x ∉ Finset.univ.image mate} : ℝ) +
        ∑ q : {q // q ∈ S}, 4 * P.mP q *
          (2 * (‖P.g q‖ ^ 2 - ‖P.h q‖ ^ 2 - ‖P.fM (mate q)‖ ^ 2) +
            (P.mergeMixed S mate).diagForm (P.fM (mate q)) +
            (P.mergeMixed S mate).diagForm (P.h q) - (P.mergeMixed S mate).diagForm (P.g q)) := by
  have hm₂' : ∀ i, 2 ≤ (P.mergeMixed S mate).m₂ i := by
    rintro (i | q)
    · exact hm₂ i
    · show 2 ≤ 2 * P.mP q + 1; linarith [hmP q]
  have h1 := P.four_mass_sub_energy_le_merge S mate hmate
  have h2 := (P.mergeMixed S mate).four_mass_sub_energy_le_card_add_card hm₂'
    (fun q => hmP q) hH (fun x => hMn x)
  linarith

end Merge

end HorizontalPacket

end GaloisForLFunctions.HilbertMetric
