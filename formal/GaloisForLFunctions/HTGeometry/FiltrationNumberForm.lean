import Mathlib

/-!
# Number forms attached to a filtration, and their norm-equivalence

A filtration `E 0 ⊆ E 1 ⊆ ⋯` of a vector space carries a canonical nonnegative quadratic functional

```text
N(f) = ∑_{n ≥ 0} dist(f, E n)²,
```

the *number form* of the filtration.  Three facts are proved here.

* **Comparison.**  If two nonnegative costs satisfy `c·Q₁ ≤ Q₂ ≤ C·Q₁` pointwise, then the same
  two-sided bound holds for the distances to every member of the filtration, hence for the number
  forms.  In particular the two number forms have the *same* finiteness domain.

* **The spectral identity.**  When the cost is the squared norm of a Hilbert space and the
  filtration is the family of initial-segment spans of an orthonormal basis, the number form is
  exactly `∑_j j·|c_j|²`, the diagonal number operator in that basis.  The proof is the exchange of
  two nonnegative sums, `#{n : n < j} = j`.

* **The bounded energy representative.**  A symmetric continuous bilinear form dominated on the
  diagonal by the squared norm is dominated everywhere by `‖x‖·‖y‖`, and is therefore represented by
  a self-adjoint contraction.  No self-adjoint extension of an underlying (possibly indefinite)
  operator is needed.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators InnerProductSpace ENNReal

/-! ## Distance to a member of the filtration -/

section Cost

variable {V W : Type*} [AddCommGroup V]

/-- The infimum of a nonnegative cost `Q` over the displacements `f - q` with `q` ranging over a
set `S`.  For `Q = ‖·‖²` this is the squared distance from `f` to `S`. -/
noncomputable def filtCost (Q : V → ℝ) (S : Set V) (f : V) : ℝ :=
  sInf ((fun q => Q (f - q)) '' S)

variable {Q Q₁ Q₂ : V → ℝ} {S : Set V} {f : V} {c C : ℝ}

theorem bddBelow_costImage (hQ : ∀ x, 0 ≤ Q x) (S : Set V) (f : V) :
    BddBelow ((fun q => Q (f - q)) '' S) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨q, _, rfl⟩
  exact hQ _

theorem filtCost_nonneg (hQ : ∀ x, 0 ≤ Q x) : 0 ≤ filtCost Q S f := by
  refine Real.sInf_nonneg ?_
  rintro _ ⟨q, _, rfl⟩
  exact hQ _

theorem filtCost_le (hQ : ∀ x, 0 ≤ Q x) {q : V} (hq : q ∈ S) : filtCost Q S f ≤ Q (f - q) :=
  csInf_le (bddBelow_costImage hQ S f) ⟨q, hq, rfl⟩

theorem le_filtCost {r : ℝ} (hne : S.Nonempty) (h : ∀ q ∈ S, r ≤ Q (f - q)) :
    r ≤ filtCost Q S f := by
  refine le_csInf (hne.image _) ?_
  rintro _ ⟨q, hq, rfl⟩
  exact h q hq

/-- A pointwise lower comparison of costs descends to the distances. -/
theorem mul_filtCost_le (hQ₁ : ∀ x, 0 ≤ Q₁ x) (hc : 0 ≤ c) (h : ∀ x, c * Q₁ x ≤ Q₂ x)
    (hne : S.Nonempty) : c * filtCost Q₁ S f ≤ filtCost Q₂ S f := by
  refine le_filtCost hne fun q hq => ?_
  exact le_trans (mul_le_mul_of_nonneg_left (filtCost_le hQ₁ hq) hc) (h _)

/-- A pointwise upper comparison of costs descends to the distances. -/
theorem filtCost_le_mul (hQ₂ : ∀ x, 0 ≤ Q₂ x) (hC : 0 < C)
    (h : ∀ x, Q₂ x ≤ C * Q₁ x) (hne : S.Nonempty) :
    filtCost Q₂ S f ≤ C * filtCost Q₁ S f := by
  have hdiv : filtCost Q₂ S f / C ≤ filtCost Q₁ S f := by
    refine le_filtCost hne fun q hq => ?_
    rw [div_le_iff₀ hC]
    have h1 := filtCost_le hQ₂ (f := f) hq
    have h2 := h (f - q)
    nlinarith
  calc filtCost Q₂ S f = filtCost Q₂ S f / C * C := by field_simp
    _ ≤ filtCost Q₁ S f * C := mul_le_mul_of_nonneg_right hdiv hC.le
    _ = C * filtCost Q₁ S f := by ring

/-- The cost of a linearly transported filtration is the transported cost. -/
theorem filtCost_comp_addMonoidHom [AddCommGroup W] (T : V →+ W) (Q : W → ℝ) (S : Set V) (f : V) :
    filtCost (fun x => Q (T x)) S f = filtCost Q (T '' S) (T f) := by
  unfold filtCost
  congr 1
  ext r
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨T q, ⟨q, hq, rfl⟩, by show Q (T f - T q) = Q (T (f - q)); rw [map_sub]⟩
  · rintro ⟨w, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨q, hq, by show Q (T (f - q)) = Q (T f - T q); rw [map_sub]⟩

end Cost

/-! ## The number form of a filtration -/

section Form

variable {V : Type*} [AddCommGroup V] {Q Q₁ Q₂ : V → ℝ} {E : ℕ → Set V} {f : V} {c C : ℝ}

/-- The number form of a filtration: the total squared distance to all of its members. -/
noncomputable def filtForm (Q : V → ℝ) (E : ℕ → Set V) (f : V) : ℝ≥0∞ :=
  ∑' n, ENNReal.ofReal (filtCost Q (E n) f)

theorem mul_filtForm_le (hQ₁ : ∀ x, 0 ≤ Q₁ x) (hc : 0 ≤ c) (h : ∀ x, c * Q₁ x ≤ Q₂ x)
    (hne : ∀ n, (E n).Nonempty) :
    ENNReal.ofReal c * filtForm Q₁ E f ≤ filtForm Q₂ E f := by
  rw [filtForm, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun n => ?_
  rw [← ENNReal.ofReal_mul hc]
  exact ENNReal.ofReal_le_ofReal (mul_filtCost_le hQ₁ hc h (hne n))

theorem filtForm_le_mul (hQ₂ : ∀ x, 0 ≤ Q₂ x) (hC : 0 < C)
    (h : ∀ x, Q₂ x ≤ C * Q₁ x) (hne : ∀ n, (E n).Nonempty) :
    filtForm Q₂ E f ≤ ENNReal.ofReal C * filtForm Q₁ E f := by
  rw [filtForm, filtForm, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun n => ?_
  rw [← ENNReal.ofReal_mul hC.le]
  exact ENNReal.ofReal_le_ofReal (filtCost_le_mul hQ₂ hC h (hne n))

/-- **Equality of the number-form domains.**  Two-sided comparability of the costs makes the two
number forms finite on exactly the same vectors. -/
theorem filtForm_ne_top_iff (hQ₁ : ∀ x, 0 ≤ Q₁ x) (hQ₂ : ∀ x, 0 ≤ Q₂ x) (hc : 0 < c) (hC : 0 < C)
    (h₁ : ∀ x, c * Q₁ x ≤ Q₂ x) (h₂ : ∀ x, Q₂ x ≤ C * Q₁ x) (hne : ∀ n, (E n).Nonempty) :
    filtForm Q₁ E f ≠ ⊤ ↔ filtForm Q₂ E f ≠ ⊤ := by
  constructor
  · intro h1
    refine ne_top_of_le_ne_top ?_ (filtForm_le_mul hQ₂ hC h₂ hne)
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top h1
  · intro h2
    have hle := mul_filtForm_le hQ₁ hc.le h₁ hne (E := E) (f := f)
    have hfin : ENNReal.ofReal c * filtForm Q₁ E f ≠ ⊤ := ne_top_of_le_ne_top h2 hle
    intro htop
    rw [htop, ENNReal.mul_top (by simpa using hc)] at hfin
    exact hfin rfl

/-- **Quantitative equivalence of the number forms.**  This is the filtration form of the card's
two-sided density comparison: comparable costs give comparable number forms with the same
constants, and hence a common form domain. -/
theorem filtForm_equivalence (hQ₁ : ∀ x, 0 ≤ Q₁ x) (hQ₂ : ∀ x, 0 ≤ Q₂ x) (hc : 0 < c) (hC : 0 < C)
    (h₁ : ∀ x, c * Q₁ x ≤ Q₂ x) (h₂ : ∀ x, Q₂ x ≤ C * Q₁ x) (hne : ∀ n, (E n).Nonempty) :
    ENNReal.ofReal c * filtForm Q₁ E f ≤ filtForm Q₂ E f ∧
      filtForm Q₂ E f ≤ ENNReal.ofReal C * filtForm Q₁ E f ∧
      (filtForm Q₁ E f ≠ ⊤ ↔ filtForm Q₂ E f ≠ ⊤) :=
  ⟨mul_filtForm_le hQ₁ hc.le h₁ hne, filtForm_le_mul hQ₂ hC h₂ hne,
    filtForm_ne_top_iff hQ₁ hQ₂ hc hC h₁ h₂ hne⟩

end Form

/-- The number form of a transported filtration is the transported number form. -/
theorem filtForm_comp_addMonoidHom {V W : Type*} [AddCommGroup V] [AddCommGroup W] (T : V →+ W)
    (Q : W → ℝ) (E : ℕ → Set V) (f : V) :
    filtForm (fun x => Q (T x)) E f = filtForm Q (fun n => T '' E n) (T f) :=
  tsum_congr fun n => by rw [filtCost_comp_addMonoidHom]

/-! ## The spectral identity in an orthonormal basis -/

section Hilbert

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The initial-segment filtration attached to an orthonormal basis. -/
def basisFiltration (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) : Submodule 𝕜 H :=
  Submodule.span 𝕜 (b '' {j | j ≤ n})

theorem summable_repr_normSq (b : HilbertBasis ℕ 𝕜 H) (x : H) :
    Summable fun j => ‖b.repr x j‖ ^ 2 := by
  have h := lp.memℓp (b.repr x)
  rw [memℓp_gen_iff (by norm_num)] at h
  simpa using h

/-- Parseval's identity in the basis. -/
theorem norm_sq_eq_tsum_repr (b : HilbertBasis ℕ 𝕜 H) (x : H) :
    ‖x‖ ^ 2 = ∑' j, ‖b.repr x j‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (b.repr x)
  have hn : ‖b.repr x‖ = ‖x‖ := b.repr.norm_map x
  rw [hn] at h
  simpa using h

theorem repr_sub_apply (b : HilbertBasis ℕ 𝕜 H) (x y : H) (j : ℕ) :
    b.repr (x - y) j = b.repr x j - b.repr y j := by
  simp only [HilbertBasis.repr_apply_apply, inner_sub_right]

/-- Vectors of the `n`-th filtration step have no coordinates beyond index `n`. -/
theorem repr_eq_zero_of_mem_basisFiltration (b : HilbertBasis ℕ 𝕜 H) {n : ℕ} {x : H}
    (hx : x ∈ basisFiltration b n) {j : ℕ} (hj : n < j) : b.repr x j = 0 := by
  classical
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      rw [HilbertBasis.repr_apply_apply, (orthonormal_iff_ite.mp b.orthonormal) j i]
      simp only [Set.mem_setOf_eq] at hi
      rw [if_neg (by omega)]
  | zero => simp
  | add y z _ _ ihy ihz =>
      have hadd : b.repr (y + z) j = b.repr y j + b.repr z j := by
        simp only [HilbertBasis.repr_apply_apply, inner_add_right]
      rw [hadd, ihy, ihz, add_zero]
  | smul r y _ ihy =>
      have hsm : b.repr (r • y) j = r * b.repr y j := by
        simp only [HilbertBasis.repr_apply_apply, inner_smul_right]
      rw [hsm, ihy, mul_zero]

/-- The truncation of `f` to the `n`-th filtration step. -/
noncomputable def basisTruncation (b : HilbertBasis ℕ 𝕜 H) (f : H) (n : ℕ) : H :=
  ∑ i ∈ Finset.range (n + 1), b.repr f i • b i

theorem basisTruncation_mem (b : HilbertBasis ℕ 𝕜 H) (f : H) (n : ℕ) :
    basisTruncation b f n ∈ basisFiltration b n := by
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨i, by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hi, rfl⟩

theorem repr_basisTruncation (b : HilbertBasis ℕ 𝕜 H) (f : H) (n j : ℕ) :
    b.repr (basisTruncation b f n) j = if j ≤ n then b.repr f j else 0 := by
  classical
  have hij : ∀ i j : ℕ, (inner 𝕜 (b i) (b j)) = if i = j then (1 : 𝕜) else 0 :=
    fun i j => (orthonormal_iff_ite.mp b.orthonormal) i j
  rw [basisTruncation, HilbertBasis.repr_apply_apply, inner_sum]
  simp only [inner_smul_right, hij, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq (Finset.range (n + 1)) j (fun i => (b.repr f) i)]
  simp

/-- The tail energy of `f` beyond index `n`. -/
noncomputable def reprTail (b : HilbertBasis ℕ 𝕜 H) (f : H) (n : ℕ) : ℝ :=
  ∑' j, if n < j then ‖b.repr f j‖ ^ 2 else 0

theorem summable_reprTail_terms (b : HilbertBasis ℕ 𝕜 H) (f : H) (n : ℕ) :
    Summable fun j => if n < j then ‖b.repr f j‖ ^ 2 else 0 := by
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) (summable_repr_normSq b f)
  · by_cases hj : n < j <;> simp [hj]
  · by_cases hj : n < j <;> simp [hj]

theorem reprTail_nonneg (b : HilbertBasis ℕ 𝕜 H) (f : H) (n : ℕ) : 0 ≤ reprTail b f n := by
  refine tsum_nonneg fun j => ?_
  by_cases hj : n < j <;> simp [hj]

theorem reprTail_le_norm_sq_sub (b : HilbertBasis ℕ 𝕜 H) (f : H) (n : ℕ) {q : H}
    (hq : q ∈ basisFiltration b n) : reprTail b f n ≤ ‖f - q‖ ^ 2 := by
  rw [norm_sq_eq_tsum_repr b (f - q)]
  refine Summable.tsum_le_tsum (fun j => ?_) (summable_reprTail_terms b f n)
    (summable_repr_normSq b (f - q))
  by_cases hj : n < j
  · rw [if_pos hj, repr_sub_apply, repr_eq_zero_of_mem_basisFiltration b hq hj, sub_zero]
  · rw [if_neg hj]
    positivity

theorem norm_sq_sub_basisTruncation (b : HilbertBasis ℕ 𝕜 H) (f : H) (n : ℕ) :
    ‖f - basisTruncation b f n‖ ^ 2 = reprTail b f n := by
  rw [norm_sq_eq_tsum_repr b (f - basisTruncation b f n), reprTail]
  refine tsum_congr fun j => ?_
  rw [repr_sub_apply, repr_basisTruncation]
  by_cases hj : n < j
  · rw [if_pos hj, if_neg (by omega), sub_zero]
  · rw [if_neg hj, if_pos (by omega), sub_self, norm_zero]
    norm_num

/-- **The distance to the `n`-th filtration step is the tail energy.** -/
theorem filtCost_normSq_basisFiltration (b : HilbertBasis ℕ 𝕜 H) (f : H) (n : ℕ) :
    filtCost (fun x => ‖x‖ ^ 2) (basisFiltration b n : Set H) f = reprTail b f n := by
  refine le_antisymm ?_ ?_
  · have h := filtCost_le (Q := fun x : H => ‖x‖ ^ 2) (f := f) (fun x => sq_nonneg _)
      (basisTruncation_mem b f n)
    rwa [norm_sq_sub_basisTruncation] at h
  · exact le_filtCost ⟨0, (basisFiltration b n).zero_mem⟩ fun q hq => reprTail_le_norm_sq_sub b f n hq

/-- **The number form of the basis filtration is the diagonal number operator.**  Summing the tail
energies and exchanging the two nonnegative sums replaces `#{n : n < j}` by `j`. -/
theorem filtForm_normSq_basisFiltration (b : HilbertBasis ℕ 𝕜 H) (f : H) :
    filtForm (fun x => ‖x‖ ^ 2) (fun n => (basisFiltration b n : Set H)) f
      = ∑' j : ℕ, (j : ℝ≥0∞) * ENNReal.ofReal (‖b.repr f j‖ ^ 2) := by
  classical
  have hcost : ∀ n, ENNReal.ofReal (filtCost (fun x : H => ‖x‖ ^ 2)
      (basisFiltration b n : Set H) f)
      = ∑' j : ℕ, (if n < j then ENNReal.ofReal (‖b.repr f j‖ ^ 2) else 0) := by
    intro n
    rw [filtCost_normSq_basisFiltration, reprTail,
      ENNReal.ofReal_tsum_of_nonneg (fun j => by by_cases hj : n < j <;> simp [hj])
        (summable_reprTail_terms b f n)]
    refine tsum_congr fun j => ?_
    by_cases hj : n < j <;> simp [hj]
  rw [filtForm, tsum_congr hcost, ENNReal.tsum_comm]
  refine tsum_congr fun j => ?_
  have hvanish : ∀ n ∉ Finset.range j,
      (if n < j then ENNReal.ofReal (‖b.repr f j‖ ^ 2) else 0) = 0 := by
    intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    rw [if_neg (by omega)]
  rw [tsum_eq_sum hvanish,
    Finset.sum_congr rfl (fun n hn => if_pos (Finset.mem_range.mp hn)),
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end Hilbert

/-! ## Number-form equivalence for two comparable Hilbert realisations -/

section Comparison

variable {𝕜 V H₁ H₂ : Type*} [RCLike 𝕜] [AddCommGroup V]
  [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]

/-- The number form of a Hilbert realisation of a filtration is the diagonal number operator of the
corresponding orthonormal basis. -/
theorem filtForm_realization (T : V →+ H₁) (b : HilbertBasis ℕ 𝕜 H₁) (E : ℕ → Set V)
    (hE : ∀ n, T '' E n = (basisFiltration b n : Set H₁)) (f : V) :
    filtForm (fun x => ‖T x‖ ^ 2) E f
      = ∑' j : ℕ, (j : ℝ≥0∞) * ENNReal.ofReal (‖b.repr (T f) j‖ ^ 2) := by
  rw [filtForm_comp_addMonoidHom T (fun y : H₁ => ‖y‖ ^ 2) E f, funext hE]
  exact filtForm_normSq_basisFiltration b (T f)

/-- **Number-form equivalence.**  Two comparable Hilbert realisations of one filtration have number
forms that are the diagonal number operators of their respective orthonormal bases, are equivalent
with the comparison constants of the norms, and have a common finiteness domain. -/
theorem number_form_equivalence (T₁ : V →+ H₁) (T₂ : V →+ H₂)
    (b₁ : HilbertBasis ℕ 𝕜 H₁) (b₂ : HilbertBasis ℕ 𝕜 H₂) (E : ℕ → Set V)
    (hne : ∀ n, (E n).Nonempty)
    (hE₁ : ∀ n, T₁ '' E n = (basisFiltration b₁ n : Set H₁))
    (hE₂ : ∀ n, T₂ '' E n = (basisFiltration b₂ n : Set H₂))
    {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (h₁ : ∀ x : V, c * ‖T₁ x‖ ^ 2 ≤ ‖T₂ x‖ ^ 2)
    (h₂ : ∀ x : V, ‖T₂ x‖ ^ 2 ≤ C * ‖T₁ x‖ ^ 2) (f : V) :
    filtForm (fun x => ‖T₁ x‖ ^ 2) E f
        = ∑' j : ℕ, (j : ℝ≥0∞) * ENNReal.ofReal (‖b₁.repr (T₁ f) j‖ ^ 2) ∧
      filtForm (fun x => ‖T₂ x‖ ^ 2) E f
        = ∑' j : ℕ, (j : ℝ≥0∞) * ENNReal.ofReal (‖b₂.repr (T₂ f) j‖ ^ 2) ∧
      ENNReal.ofReal c * filtForm (fun x => ‖T₁ x‖ ^ 2) E f
        ≤ filtForm (fun x => ‖T₂ x‖ ^ 2) E f ∧
      filtForm (fun x => ‖T₂ x‖ ^ 2) E f
        ≤ ENNReal.ofReal C * filtForm (fun x => ‖T₁ x‖ ^ 2) E f ∧
      (filtForm (fun x => ‖T₁ x‖ ^ 2) E f ≠ ⊤ ↔ filtForm (fun x => ‖T₂ x‖ ^ 2) E f ≠ ⊤) := by
  refine ⟨filtForm_realization T₁ b₁ E hE₁ f, filtForm_realization T₂ b₂ E hE₂ f, ?_, ?_, ?_⟩
  · exact mul_filtForm_le (fun x => sq_nonneg _) hc.le h₁ hne
  · exact filtForm_le_mul (fun x => sq_nonneg _) hC h₂ hne
  · exact filtForm_ne_top_iff (fun x => sq_nonneg _) (fun x => sq_nonneg _) hc hC h₁ h₂ hne

end Comparison

/-! ## The bounded energy representative -/

section EnergyForm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- **A symmetric form dominated on the diagonal is dominated everywhere.**  The parallelogram law
gives `|B x y| ≤ (‖x‖² + ‖y‖²)/2`; rescaling `x ↦ t x`, `y ↦ t⁻¹ y` and optimising in `t` sharpens
this to the product bound. -/
theorem abs_bilin_le_of_abs_diagonal_le (B : H →L[ℝ] H →L[ℝ] ℝ)
    (hsymm : ∀ x y, B x y = B y x) (hdiag : ∀ x, |B x x| ≤ ‖x‖ ^ 2) (x y : H) :
    |B x y| ≤ ‖x‖ * ‖y‖ := by
  have key : ∀ u v : H, |B u v| ≤ (‖u‖ ^ 2 + ‖v‖ ^ 2) / 2 := by
    intro u v
    have h4 : (4 : ℝ) * B u v = B (u + v) (u + v) - B (u - v) (u - v) := by
      simp only [map_add, map_sub, add_apply, sub_apply]
      linarith [hsymm u v]
    have hpar : ‖u + v‖ ^ 2 + ‖u - v‖ ^ 2 = 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) :=
      parallelogram_law_with_norm ℝ u v
    have h1 := hdiag (u + v)
    have h2 := hdiag (u - v)
    have habs : |(4 : ℝ) * B u v| ≤ ‖u + v‖ ^ 2 + ‖u - v‖ ^ 2 := by
      rw [h4]
      exact le_trans (abs_sub _ _) (add_le_add h1 h2)
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)] at habs
    linarith
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  set t : ℝ := Real.sqrt (‖y‖ / ‖x‖) with ht
  have htpos : 0 < t := Real.sqrt_pos.mpr (div_pos hyn hxn)
  have hts : t ^ 2 = ‖y‖ / ‖x‖ := Real.sq_sqrt (le_of_lt (div_pos hyn hxn))
  have hscale : B (t • x) (t⁻¹ • y) = B x y := by
    rw [map_smul B t x, smul_apply, map_smul (B x) t⁻¹ y, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, mul_inv_cancel₀ htpos.ne', one_mul]
  have hb := key (t • x) (t⁻¹ • y)
  rw [hscale, norm_smul, norm_smul] at hb
  have h1 : (‖t‖ * ‖x‖) ^ 2 = ‖y‖ * ‖x‖ := by
    rw [Real.norm_eq_abs, abs_of_pos htpos, mul_pow, hts]
    field_simp
  have h2 : (‖t⁻¹‖ * ‖y‖) ^ 2 = ‖x‖ * ‖y‖ := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr htpos), mul_pow, inv_pow, hts]
    field_simp
  rw [h1, h2] at hb
  calc |B x y| ≤ (‖y‖ * ‖x‖ + ‖x‖ * ‖y‖) / 2 := hb
    _ = ‖x‖ * ‖y‖ := by ring

/-- The Riesz representative of a continuous bilinear form, as a linear map. -/
noncomputable def formRieszMap (B : H →L[ℝ] H →L[ℝ] ℝ) : H →ₗ[ℝ] H where
  toFun x := (InnerProductSpace.toDual ℝ H).symm (B x)
  map_add' x y := by
    refine ext_inner_right ℝ fun v => ?_
    simp [InnerProductSpace.toDual_symm_apply, inner_add_left]
  map_smul' r x := by
    refine ext_inner_right ℝ fun v => ?_
    simp [InnerProductSpace.toDual_symm_apply, real_inner_smul_left]

@[simp] theorem inner_formRieszMap (B : H →L[ℝ] H →L[ℝ] ℝ) (x y : H) :
    ⟪formRieszMap B x, y⟫_ℝ = B x y :=
  InnerProductSpace.toDual_symm_apply

theorem norm_formRieszMap (B : H →L[ℝ] H →L[ℝ] ℝ) (x : H) : ‖formRieszMap B x‖ = ‖B x‖ :=
  (InnerProductSpace.toDual ℝ H).symm.norm_map (B x)

/-- The Riesz representative of a continuous bilinear form, as a continuous linear map. -/
noncomputable def formRiesz (B : H →L[ℝ] H →L[ℝ] ℝ) : H →L[ℝ] H :=
  (formRieszMap B).mkContinuous ‖B‖ fun x => by
    rw [show (formRieszMap B) x = formRieszMap B x from rfl, norm_formRieszMap]
    exact B.le_opNorm x

@[simp] theorem inner_formRiesz (B : H →L[ℝ] H →L[ℝ] ℝ) (x y : H) :
    ⟪formRiesz B x, y⟫_ℝ = B x y :=
  inner_formRieszMap B x y

theorem isSelfAdjoint_formRiesz {B : H →L[ℝ] H →L[ℝ] ℝ} (hsymm : ∀ x y, B x y = B y x) :
    IsSelfAdjoint (formRiesz B) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  simp only [ContinuousLinearMap.coe_coe]
  rw [inner_formRiesz, real_inner_comm, inner_formRiesz]
  exact hsymm x y

theorem norm_formRiesz_le_one {B : H →L[ℝ] H →L[ℝ] ℝ}
    (hb : ∀ x y, |B x y| ≤ ‖x‖ * ‖y‖) : ‖formRiesz B‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul]
  have hsq : ‖formRiesz B x‖ ^ 2 = B x (formRiesz B x) := by
    rw [← inner_formRiesz B x (formRiesz B x), real_inner_self_eq_norm_sq]
  have hle : ‖formRiesz B x‖ ^ 2 ≤ ‖x‖ * ‖formRiesz B x‖ := by
    rw [hsq]
    exact le_trans (le_abs_self _) (hb x (formRiesz B x))
  rcases eq_or_lt_of_le (norm_nonneg (formRiesz B x)) with h | h
  · rw [← h]; exact norm_nonneg x
  · nlinarith

/-- **The bounded energy representative.**  A symmetric continuous bilinear form whose diagonal is
dominated by the energy norm is represented by a self-adjoint contraction of the energy space.  No
self-adjoint realisation of an underlying indefinite operator is required. -/
theorem exists_energy_contraction (B : H →L[ℝ] H →L[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (hdiag : ∀ x, |B x x| ≤ ‖x‖ ^ 2) :
    ∃ C : H →L[ℝ] H, IsSelfAdjoint C ∧ ‖C‖ ≤ 1 ∧ ∀ x y, B x y = ⟪x, C y⟫_ℝ := by
  refine ⟨formRiesz B, isSelfAdjoint_formRiesz hsymm,
    norm_formRiesz_le_one (abs_bilin_le_of_abs_diagonal_le B hsymm hdiag), fun x y => ?_⟩
  rw [real_inner_comm, inner_formRiesz]
  exact hsymm x y

end EnergyForm

end GaloisForLFunctions.HTGeometry
