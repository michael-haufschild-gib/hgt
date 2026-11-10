import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheSquareOfACyclotomicRingHasItsContactsOnAProgression
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheHodgeDefectIsCyclic

/-!
# The Hodge index of a number ring counts the zeros of its zeta function

The zeta function of an abelian number ring is `ζ(s) Π_i L(s, χ_i)` over primitive characters,
and the defect of the inequality of Castelnuovo and Severi on its square is the sum of Weil's
forms of `ζ` and of the `L(s, χ_i)`. The index law bounds the negative squares of the sum by
the sum of the numbers of zeros to the right of the line. Here the bound is replaced by an
equality, and the square of a ring is compared with the square of the integers under it.

* **Superposition** (`superposeFamily`, `W_superposeFamily`, `temperedConfig_superposeFamily`,
  `rightZeros_superposeFamily`). A finite family of zero configurations has a superposition:
  the union of the zeros, with the multiplicities added. Its Weil form is the sum of the forms,
  it is tempered when the members are, and its zeros to the right of the line are the union.
  No disjointness is assumed: a zero common to two members is one point with the sum of the
  multiplicities.
* **The exact index of a sum of forms** (`exists_le_negIndex_sum_zeroGram_iff`). The sum of
  Weil's forms of finitely many tempered configurations has `n` negative squares on some family
  of `n` tests iff the configurations have, together, at least `n` distinct zeros to the right
  of the line.
* **The square of a number ring** (`exists_le_negIndex_ringDefect_iff`). The defect of the
  square of the ring with the characters `χ_i` has `n` negative squares on some family of `n`
  tests iff `ζ` and the `L(s, χ_i)` have at least `n` distinct zeros to the right of the line:
  the Hodge index of the ring is the number of these zeros.
* **A cover bounds its base** (`exists_le_negIndex_ringDefect_of_zeta`,
  `forall_negIndex_ringDefect_eq_zero_iff`, `riemannHypothesis_of_ringDefect`). Negative squares
  of the square of the integers are negative squares of the square of every ring over it. The
  inequality of Castelnuovo and Severi holds on the square of the ring iff neither `ζ` nor any
  `L(s, χ_i)` has a zero to the right of the line; in particular it implies the Riemann
  hypothesis.

Each isotypic part has its own exact index, the number of zeros of its `L`-function to the
right of the line (corpus: `ArithmeticCastelnuovoSeveri.pontryagin_law`); the index of the ring
is at most the sum of the indices of the parts, with equality iff no zero to the right of the
line is shared.
-/

open Finset Filter Topology MeasureTheory Matrix
open Zeta23 GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### The superposition of a family of configurations -/

section Superposition

variable {κ : Type*} [Fintype κ]

open Classical in
/-- The superposition of a finite family of zero configurations: the union of the zeros, with
the multiplicities added. -/
def superposeFamily (Z : κ → ZeroConfig) : ZeroConfig where
  carrier := ⋃ i, (Z i).carrier
  mult := fun ρ => ∑ i, if ρ ∈ (Z i).carrier then (Z i).mult ρ else 0
  one_le_mult := by
    intro ρ hρ
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hρ
    have h1 := (Z i).one_le_mult ρ hi
    have h2 : (if ρ ∈ (Z i).carrier then (Z i).mult ρ else 0) ≤
        ∑ j, if ρ ∈ (Z j).carrier then (Z j).mult ρ else 0 :=
      Finset.single_le_sum (f := fun j => if ρ ∈ (Z j).carrier then (Z j).mult ρ else 0)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [if_pos hi] at h2
    exact h1.trans h2
  strip := by
    intro ρ hρ
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hρ
    exact (Z i).strip ρ hi
  reflect_mem := by
    intro ρ hρ
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hρ
    exact Set.mem_iUnion.mpr ⟨i, (Z i).reflect_mem ρ hi⟩
  mult_reflect := by
    intro ρ _
    refine Finset.sum_congr rfl fun i _ => ?_
    have hrr : reflect (reflect ρ) = ρ := by simp [reflect]
    by_cases h : ρ ∈ (Z i).carrier
    · rw [if_pos ((Z i).reflect_mem ρ h), if_pos h, (Z i).mult_reflect ρ h]
    · have h' : reflect ρ ∉ (Z i).carrier := fun h' => h (hrr ▸ (Z i).reflect_mem _ h')
      rw [if_neg h', if_neg h]
  finite_window := fun T₁ T₂ => by
    refine (Set.finite_iUnion fun i => (Z i).finite_window T₁ T₂).subset ?_
    rintro ρ ⟨h1, h2⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h1
    exact Set.mem_iUnion.mpr ⟨i, hi, h2⟩

/-- **A sum over a superposition is the sum of the sums.** For a function `F` of the zero, the
series `Σ_ρ m_ρ F(ρ)` over the superposition is the sum of the series over the members; common
zeros are regrouped through the indicators of the carriers. -/
theorem hasSum_superposeFamily (Z : κ → ZeroConfig) {α : Type*} [AddCommMonoid α]
    [TopologicalSpace α] [ContinuousAdd α] (F : ℂ → α) {A : κ → α}
    (h : ∀ i, HasSum (fun ρ : (Z i).carrier => (Z i).mult ρ • F ρ) (A i)) :
    HasSum (fun ρ : (superposeFamily Z).carrier => (superposeFamily Z).mult ρ • F ρ)
      (∑ i, A i) := by
  classical
  have key : ∀ i, HasSum ((Z i).carrier.indicator fun ρ => (Z i).mult ρ • F ρ) (A i) :=
    fun i => (hasSum_subtype_iff_indicator (f := fun ρ => (Z i).mult ρ • F ρ)).mp (h i)
  have hsum : HasSum (fun ρ => ∑ i, (Z i).carrier.indicator (fun ρ => (Z i).mult ρ • F ρ) ρ)
      (∑ i, A i) := hasSum_sum fun i _ => key i
  refine (hasSum_subtype_iff_indicator
    (f := fun ρ => (superposeFamily Z).mult ρ • F ρ)).mpr ?_
  convert hsum using 1
  funext ρ
  by_cases hρ : ρ ∈ (superposeFamily Z).carrier
  · rw [Set.indicator_of_mem hρ]
    show (∑ i, if ρ ∈ (Z i).carrier then (Z i).mult ρ else 0) • F ρ = _
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : ρ ∈ (Z i).carrier
    · rw [if_pos hi, Set.indicator_of_mem hi]
    · rw [if_neg hi, Set.indicator_of_notMem hi, zero_smul]
  · rw [Set.indicator_of_notMem hρ]
    exact (Finset.sum_eq_zero fun i _ =>
      Set.indicator_of_notMem (fun hi => hρ (Set.mem_iUnion.mpr ⟨i, hi⟩)) _).symm

theorem Wsummand_eq_nsmul (Z : ZeroConfig) (f g : ℝ → ℂ) (ρ : ℂ) :
    Z.Wsummand f g ρ = Z.mult ρ •
      (paperFT f (gammaOf ρ) * (starRingEnd ℂ) (paperFT g ((starRingEnd ℂ) (gammaOf ρ)))) := by
  rw [ZeroConfig.Wsummand, nsmul_eq_mul, mul_assoc]

/-- **Weil's form of a superposition is the sum of the forms.** -/
theorem W_superposeFamily (Z : κ → ZeroConfig)
    (hZ : ∀ i, SquareRootThreshold.TemperedConfig (Z i)) {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) : (superposeFamily Z).W f g = ∑ i, (Z i).W f g := by
  have h : ∀ i, HasSum (fun ρ : (Z i).carrier => (Z i).mult ρ •
      (paperFT f (gammaOf ρ) * (starRingEnd ℂ) (paperFT g ((starRingEnd ℂ) (gammaOf ρ)))))
      ((Z i).W f g) := fun i => by
    have hs := (ArithmeticCastelnuovoSeveri.summable_Wsummand (Z i) (hZ i) hf hfc hg hgc).hasSum
    simp only [Wsummand_eq_nsmul] at hs
    exact hs
  have ht := (hasSum_superposeFamily Z (fun ρ => paperFT f (gammaOf ρ) *
    (starRingEnd ℂ) (paperFT g ((starRingEnd ℂ) (gammaOf ρ)))) h).tsum_eq
  rw [← ht, ZeroConfig.W]
  exact tsum_congr fun ρ => Wsummand_eq_nsmul _ f g ρ

/-- A superposition of tempered configurations is tempered. -/
theorem temperedConfig_superposeFamily (Z : κ → ZeroConfig)
    (hZ : ∀ i, SquareRootThreshold.TemperedConfig (Z i)) :
    SquareRootThreshold.TemperedConfig (superposeFamily Z) := by
  have h : ∀ i, HasSum (fun ρ : (Z i).carrier => (Z i).mult ρ •
      (1 + Complex.normSq (gammaOf (ρ : ℂ)))⁻¹)
      (∑' ρ : (Z i).carrier, ((Z i).mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) :=
    fun i => by
      have hs := (hZ i).hasSum
      simp only [div_eq_mul_inv, ← nsmul_eq_mul] at hs ⊢
      exact hs
  have hsum := (hasSum_superposeFamily Z
    (fun ρ => (1 + Complex.normSq (gammaOf ρ))⁻¹) h).summable
  unfold SquareRootThreshold.TemperedConfig
  simp only [div_eq_mul_inv, ← nsmul_eq_mul]
  exact hsum

/-- The zeros of a superposition to the right of the line are the union of those of the
members. -/
theorem rightZeros_superposeFamily (Z : κ → ZeroConfig) :
    ArithmeticCastelnuovoSeveri.rightZeros (superposeFamily Z) =
      ⋃ i, ArithmeticCastelnuovoSeveri.rightZeros (Z i) := by
  ext ρ
  simp only [ArithmeticCastelnuovoSeveri.rightZeros, superposeFamily, Set.mem_setOf_eq,
    Set.mem_iUnion]
  constructor
  · rintro ⟨⟨i, hi⟩, h⟩
    exact ⟨i, hi, h⟩
  · rintro ⟨i, hi, h⟩
    exact ⟨⟨i, hi⟩, h⟩

/-- The Gram matrix of a superposition is the sum of the Gram matrices. -/
theorem zeroGram_superposeFamily {ι : Type*} (Z : κ → ZeroConfig)
    (hZ : ∀ i, SquareRootThreshold.TemperedConfig (Z i)) (F : ι → ℝ → ℂ)
    (hF : ∀ i, ContDiff ℝ 2 (F i)) (hFc : ∀ i, HasCompactSupport (F i)) :
    ArithmeticCastelnuovoSeveri.zeroGram (superposeFamily Z) F =
      ∑ k, ArithmeticCastelnuovoSeveri.zeroGram (Z k) F := by
  ext a b
  rw [Matrix.sum_apply]
  exact W_superposeFamily Z hZ (hF a) (hFc a) (hF b) (hFc b)

/-- **The exact index of a sum of forms.** The sum of Weil's forms of finitely many tempered
configurations has `n` negative squares on some family of `n` tests iff the configurations have
together at least `n` distinct zeros to the right of the critical line. -/
theorem exists_le_negIndex_sum_zeroGram_iff (Z : κ → ZeroConfig)
    (hZ : ∀ i, SquareRootThreshold.TemperedConfig (Z i)) (n : ℕ) :
    (∃ f : Fin n → ℝ → ℂ, (∀ i, ContDiff ℝ 2 (f i)) ∧ (∀ i, HasCompactSupport (f i)) ∧
        n ≤ hermNegIndex (∑ k, ArithmeticCastelnuovoSeveri.zeroGram (Z k) f)) ↔
      (n : ℕ∞) ≤ (⋃ k, ArithmeticCastelnuovoSeveri.rightZeros (Z k)).encard := by
  rw [← rightZeros_superposeFamily, ← ArithmeticCastelnuovoSeveri.pontryagin_law
    (superposeFamily Z) (temperedConfig_superposeFamily Z hZ) n]
  refine exists_congr fun f => ⟨?_, ?_⟩
  · rintro ⟨hf, hfc, h⟩
    exact ⟨hf, hfc, by rwa [zeroGram_superposeFamily Z hZ f hf hfc]⟩
  · rintro ⟨hf, hfc, h⟩
    exact ⟨hf, hfc, by rwa [← zeroGram_superposeFamily Z hZ f hf hfc]⟩

/-- **Negative squares of a member are negative squares of the sum.** -/
theorem exists_le_negIndex_sum_of_member (Z : κ → ZeroConfig)
    (hZ : ∀ i, SquareRootThreshold.TemperedConfig (Z i)) (k : κ) {n : ℕ}
    (h : ∃ f : Fin n → ℝ → ℂ, (∀ i, ContDiff ℝ 2 (f i)) ∧ (∀ i, HasCompactSupport (f i)) ∧
      n ≤ hermNegIndex (ArithmeticCastelnuovoSeveri.zeroGram (Z k) f)) :
    ∃ f : Fin n → ℝ → ℂ, (∀ i, ContDiff ℝ 2 (f i)) ∧ (∀ i, HasCompactSupport (f i)) ∧
      n ≤ hermNegIndex (∑ k, ArithmeticCastelnuovoSeveri.zeroGram (Z k) f) := by
  rw [exists_le_negIndex_sum_zeroGram_iff Z hZ n]
  exact ((ArithmeticCastelnuovoSeveri.pontryagin_law (Z k) (hZ k) n).mp h).trans
    (Set.encard_le_encard (Set.subset_iUnion _ k))

end Superposition

/-! ### The square of a number ring -/

section Ring

variable {ι : Type*} [Fintype ι] {q : ι → ℕ} [∀ i, NeZero (q i)]

/-- The configurations of the zeta function of the ring with the characters `χ_i`: the zeros of
`ζ` and of each `L(s, χ_i)`. -/
def ringConfig (hq : ∀ i, 1 < q i) {χ : ∀ i, DirichletCharacter ℂ (q i)}
    (hprim : ∀ i, (χ i).IsPrimitive) : Option ι → ZeroConfig :=
  fun o => o.elim zetaZeroConfig fun i => _root_.RHTower.dirichletZeros (hq i) (hprim i)

theorem temperedConfig_ringConfig (hq : ∀ i, 1 < q i) {χ : ∀ i, DirichletCharacter ℂ (q i)}
    (hprim : ∀ i, (χ i).IsPrimitive) (o : Option ι) :
    SquareRootThreshold.TemperedConfig (ringConfig hq hprim o) := by
  cases o with
  | none => exact SquareRootThreshold.temperedConfig_zetaZeroConfig
  | some i => exact temperedConfig_dirichletZeros (hq i) (hprim i)

/-- **The Hodge index of the square of a number ring.** The defect of the inequality of
Castelnuovo and Severi, the sum of Weil's forms of `ζ` and of the `L(s, χ_i)`, has `n` negative
squares on some family of `n` tests iff these functions have at least `n` distinct zeros to the
right of the critical line. -/
theorem exists_le_negIndex_ringDefect_iff (hq : ∀ i, 1 < q i)
    {χ : ∀ i, DirichletCharacter ℂ (q i)} (hprim : ∀ i, (χ i).IsPrimitive) (n : ℕ) :
    (∃ f : Fin n → ℝ → ℂ, (∀ i, ContDiff ℝ 2 (f i)) ∧ (∀ i, HasCompactSupport (f i)) ∧
        n ≤ hermNegIndex (ArithmeticCastelnuovoSeveri.zeroGram zetaZeroConfig f +
          ∑ i, ArithmeticCastelnuovoSeveri.zeroGram
            (_root_.RHTower.dirichletZeros (hq i) (hprim i)) f)) ↔
      (n : ℕ∞) ≤ (ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig ∪
        ⋃ i, ArithmeticCastelnuovoSeveri.rightZeros
          (_root_.RHTower.dirichletZeros (hq i) (hprim i))).encard := by
  have h := exists_le_negIndex_sum_zeroGram_iff (ringConfig hq hprim)
    (temperedConfig_ringConfig hq hprim) n
  simp only [Fintype.sum_option, Set.iUnion_option] at h
  exact h

/-- **A cover bounds its base.** Negative squares of the defect on the square of the integers
are negative squares of the defect on the square of every ring over it. -/
theorem exists_le_negIndex_ringDefect_of_zeta (hq : ∀ i, 1 < q i)
    {χ : ∀ i, DirichletCharacter ℂ (q i)} (hprim : ∀ i, (χ i).IsPrimitive) {n : ℕ}
    (h : ∃ f : Fin n → ℝ → ℂ, (∀ i, ContDiff ℝ 2 (f i)) ∧ (∀ i, HasCompactSupport (f i)) ∧
      n ≤ hermNegIndex (ArithmeticCastelnuovoSeveri.zeroGram zetaZeroConfig f)) :
    ∃ f : Fin n → ℝ → ℂ, (∀ i, ContDiff ℝ 2 (f i)) ∧ (∀ i, HasCompactSupport (f i)) ∧
      n ≤ hermNegIndex (ArithmeticCastelnuovoSeveri.zeroGram zetaZeroConfig f +
        ∑ i, ArithmeticCastelnuovoSeveri.zeroGram
          (_root_.RHTower.dirichletZeros (hq i) (hprim i)) f) := by
  rw [exists_le_negIndex_ringDefect_iff hq hprim n]
  exact ((ArithmeticCastelnuovoSeveri.pontryagin_law zetaZeroConfig
    SquareRootThreshold.temperedConfig_zetaZeroConfig n).mp h).trans
      (Set.encard_le_encard Set.subset_union_left)

/-- **Castelnuovo and Severi on the square of a ring.** The defect has no negative square on
any family of tests iff neither `ζ` nor any `L(s, χ_i)` has a zero to the right of the critical
line. -/
theorem forall_negIndex_ringDefect_eq_zero_iff (hq : ∀ i, 1 < q i)
    {χ : ∀ i, DirichletCharacter ℂ (q i)} (hprim : ∀ i, (χ i).IsPrimitive) :
    (∀ (n : ℕ) (f : Fin n → ℝ → ℂ), (∀ i, ContDiff ℝ 2 (f i)) →
        (∀ i, HasCompactSupport (f i)) →
        hermNegIndex (ArithmeticCastelnuovoSeveri.zeroGram zetaZeroConfig f +
          ∑ i, ArithmeticCastelnuovoSeveri.zeroGram
            (_root_.RHTower.dirichletZeros (hq i) (hprim i)) f) = 0) ↔
      ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig = ∅ ∧
        ∀ i, ArithmeticCastelnuovoSeveri.rightZeros
          (_root_.RHTower.dirichletZeros (hq i) (hprim i)) = ∅ := by
  classical
  constructor
  · intro h
    -- one zero to the right of the line gives one negative square
    have hempty : ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig ∪
        ⋃ i, ArithmeticCastelnuovoSeveri.rightZeros
          (_root_.RHTower.dirichletZeros (hq i) (hprim i)) = ∅ := by
      by_contra hne
      have h1 : ((1 : ℕ) : ℕ∞) ≤ (ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig ∪
          ⋃ i, ArithmeticCastelnuovoSeveri.rightZeros
            (_root_.RHTower.dirichletZeros (hq i) (hprim i))).encard := by
        rw [Nat.cast_one, Set.one_le_encard_iff_nonempty]
        exact Set.nonempty_iff_ne_empty.mpr hne
      obtain ⟨f, hf, hfc, hle⟩ := (exists_le_negIndex_ringDefect_iff hq hprim 1).mpr h1
      rw [h 1 f hf hfc] at hle
      exact absurd hle (by norm_num)
    rw [Set.union_empty_iff, Set.iUnion_eq_empty] at hempty
    exact hempty
  · rintro ⟨hζ, hL⟩ n f hf hfc
    have hle := negIndex_sum_zeroGram_le (ringConfig hq hprim)
      (temperedConfig_ringConfig hq hprim) f hf hfc
    simp only [Fintype.sum_option] at hle
    have hz : (ArithmeticCastelnuovoSeveri.rightZeros (ringConfig hq hprim none)).encard +
        ∑ i, (ArithmeticCastelnuovoSeveri.rightZeros (ringConfig hq hprim (some i))).encard =
          0 := by
      have h0 : ArithmeticCastelnuovoSeveri.rightZeros (ringConfig hq hprim none) = ∅ := hζ
      have hi : ∀ i, ArithmeticCastelnuovoSeveri.rightZeros (ringConfig hq hprim (some i)) =
          ∅ := hL
      rw [h0, Set.encard_empty, zero_add]
      exact Finset.sum_eq_zero fun i _ => by rw [hi i, Set.encard_empty]
    rw [hz] at hle
    exact Nat.eq_zero_of_le_zero (by exact_mod_cast hle)

/-- **Castelnuovo and Severi on the square of a ring imply the Riemann hypothesis.** -/
theorem riemannHypothesis_of_ringDefect (hq : ∀ i, 1 < q i)
    {χ : ∀ i, DirichletCharacter ℂ (q i)} (hprim : ∀ i, (χ i).IsPrimitive)
    (h : ∀ (n : ℕ) (f : Fin n → ℝ → ℂ), (∀ i, ContDiff ℝ 2 (f i)) →
      (∀ i, HasCompactSupport (f i)) →
      hermNegIndex (ArithmeticCastelnuovoSeveri.zeroGram zetaZeroConfig f +
        ∑ i, ArithmeticCastelnuovoSeveri.zeroGram
          (_root_.RHTower.dirichletZeros (hq i) (hprim i)) f) = 0) :
    RiemannHypothesis :=
  ArithmeticCastelnuovoSeveri.rightZeros_zeta_eq_empty_iff.mp
    ((forall_negIndex_ringDefect_eq_zero_iff hq hprim).mp h).1

end Ring

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
