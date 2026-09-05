import GaloisForLFunctions.HTGeometry.TopologicallyAdmittedGaugeAction
import GaloisForLFunctions.HTGeometry.TopologicallyAdmittedFellerTensorFracture

/-!
# Exact detector--morphism transfer for Bernoulli prefixes

This closes the concrete part of ULF-TAFM-5. It constructs the genuine binary prefix
ultrametrics, proves exact discrete and inherited prefix-map amplifications, identifies
deterministic pullback amplification with the map Lipschitz constant on bounded effects,
constructs a literal tensor Neyman--Pearson detector, and proves that both gauge allocations
have the same exact source action. It also supplies the source-price/action sandwich and exact
finite-factor localization law.

Paper source:
`docs/drafts/pipeline/3-formalized/universal-law-field/topologically-admitted-formation-mechanics/gauge-covariant-resolution-action-composition-curvature-and-detector-transfer-law.md`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

abbrev BinaryStream := ℕ → Bool
abbrev BinaryWord (d : ℕ) := Fin d → Bool

local instance : DecidableEq BinaryStream := Classical.decEq _

private theorem exists_binary_index_ne_of_ne {x y : BinaryStream} (hxy : x ≠ y) :
    ∃ n, x n ≠ y n := by
  by_contra h
  simp only [not_exists, not_not] at h
  exact hxy (funext h)

/-- First coordinate where two binary streams disagree; zero on the diagonal. -/
noncomputable def binaryFirstDisagreement (x y : BinaryStream) : ℕ :=
  if hxy : x = y then 0 else Nat.find (exists_binary_index_ne_of_ne hxy)

theorem binaryFirstDisagreement_apply_ne {x y : BinaryStream} (hxy : x ≠ y) :
    x (binaryFirstDisagreement x y) ≠ y (binaryFirstDisagreement x y) := by
  rw [binaryFirstDisagreement, dif_neg hxy]
  exact Nat.find_spec (exists_binary_index_ne_of_ne hxy)

theorem binaryFirstDisagreement_eq_before {x y : BinaryStream} (hxy : x ≠ y)
    {k : ℕ} (hk : k < binaryFirstDisagreement x y) : x k = y k := by
  by_contra hne
  rw [binaryFirstDisagreement, dif_neg hxy] at hk
  have hmin := Nat.find_min' (exists_binary_index_ne_of_ne hxy) hne
  omega

theorem binaryFirstDisagreement_eq_of_ne_of_eq_before
    {x y : BinaryStream} {m : ℕ} (hne : x m ≠ y m)
    (hbefore : ∀ k < m, x k = y k) :
    binaryFirstDisagreement x y = m := by
  have hxy : x ≠ y := fun h => hne (congrFun h m)
  apply le_antisymm
  · rw [binaryFirstDisagreement, dif_neg hxy]
    exact Nat.find_min' (exists_binary_index_ne_of_ne hxy) hne
  · by_contra hlt
    have heq := hbefore (binaryFirstDisagreement x y) (by omega)
    exact binaryFirstDisagreement_apply_ne hxy heq

theorem binaryFirstDisagreement_comm (x y : BinaryStream) :
    binaryFirstDisagreement x y = binaryFirstDisagreement y x := by
  by_cases hxy : x = y
  · subst y
    rfl
  · have hyx : y ≠ x := Ne.symm hxy
    apply le_antisymm
    · rw [binaryFirstDisagreement, dif_neg hxy]
      exact Nat.find_min' (exists_binary_index_ne_of_ne hxy)
        (Ne.symm (binaryFirstDisagreement_apply_ne hyx))
    · rw [binaryFirstDisagreement, dif_neg hyx]
      exact Nat.find_min' (exists_binary_index_ne_of_ne hyx)
        (Ne.symm (binaryFirstDisagreement_apply_ne hxy))

private def binaryPrefix (d : ℕ) (x : BinaryStream) : BinaryWord d := fun i => x i

def binaryExtend (d : ℕ) (z : BinaryWord d) : BinaryStream := fun n =>
  if h : n < d then z ⟨n, h⟩ else false

@[simp] theorem binaryPrefix_extend (d : ℕ) (z : BinaryWord d) :
    binaryPrefix d (binaryExtend d z) = z := by
  funext i
  simp [binaryPrefix, binaryExtend, i.isLt]

/-- Baire-prefix distance with ratio `θ`. -/
def binaryStreamPrefixDist (θ : ℝ) (x y : BinaryStream) : ℝ :=
  if x = y then 0 else θ ^ binaryFirstDisagreement x y

/-- Inherited finite-prefix distance. -/
def binaryWordPrefixDist (θ : ℝ) {d : ℕ} (z w : BinaryWord d) : ℝ :=
  binaryStreamPrefixDist θ (binaryExtend d z) (binaryExtend d w)

def binaryWordDiscreteDist {d : ℕ} (z w : BinaryWord d) : ℝ :=
  if z = w then 0 else 1

theorem binaryStreamPrefixDist_nonneg {θ : ℝ} (hθ : 0 ≤ θ)
    (x y : BinaryStream) : 0 ≤ binaryStreamPrefixDist θ x y := by
  rw [binaryStreamPrefixDist]
  split
  · rfl
  · exact pow_nonneg hθ _

theorem binaryWordPrefixDist_nonneg {θ : ℝ} (hθ : 0 ≤ θ)
    {d : ℕ} (z w : BinaryWord d) : 0 ≤ binaryWordPrefixDist θ z w :=
  binaryStreamPrefixDist_nonneg hθ _ _

theorem binaryStreamPrefixDist_comm (θ : ℝ) (x y : BinaryStream) :
    binaryStreamPrefixDist θ x y = binaryStreamPrefixDist θ y x := by
  by_cases hxy : x = y
  · subst y
    rfl
  · simp [binaryStreamPrefixDist, hxy, Ne.symm hxy,
      binaryFirstDisagreement_comm]

theorem pow_antitone_of_nonneg_of_le_one {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    {m n : ℕ} (hmn : m ≤ n) : θ ^ n ≤ θ ^ m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [pow_add]
  have hk : θ ^ k ≤ 1 := pow_le_one₀ hθ0 hθ1
  exact (mul_le_mul_of_nonneg_left hk (pow_nonneg hθ0 m)).trans_eq (mul_one _)

/-- Metric axioms in strong-triangle form for a real-valued distance. -/
structure RealUltrametricLaw {A : Type*} (distA : A → A → ℝ) : Prop where
  nonneg : ∀ x y, 0 ≤ distA x y
  eq_zero_iff : ∀ x y, distA x y = 0 ↔ x = y
  symm : ∀ x y, distA x y = distA y x
  strong_triangle : ∀ x y z, distA x z ≤ max (distA x y) (distA y z)

theorem binaryStreamPrefixDist_ultrametric
    {θ : ℝ} (hθ : 0 < θ) (hθ₁ : θ < 1) :
    RealUltrametricLaw (binaryStreamPrefixDist θ) where
  nonneg := binaryStreamPrefixDist_nonneg hθ.le
  eq_zero_iff := by
    intro x y
    constructor
    · intro hzero
      by_contra hxy
      rw [binaryStreamPrefixDist, if_neg hxy] at hzero
      exact (pow_pos hθ _).ne' hzero
    · rintro rfl
      simp [binaryStreamPrefixDist]
  symm := binaryStreamPrefixDist_comm θ
  strong_triangle := by
    intro x y z
    by_cases hxz : x = z
    · subst z
      rw [binaryStreamPrefixDist, if_pos rfl]
      exact (binaryStreamPrefixDist_nonneg hθ.le y x).trans
        (le_max_right _ _)
    · let m := binaryFirstDisagreement x z
      have hmne : x m ≠ z m := binaryFirstDisagreement_apply_ne hxz
      have hor : x m ≠ y m ∨ y m ≠ z m := by
        by_cases hxy : x m = y m
        · exact Or.inr (fun hyz => hmne (hxy.trans hyz))
        · exact Or.inl hxy
      rw [binaryStreamPrefixDist, if_neg hxz]
      rcases hor with hxy | hyz
      · have hXY : x ≠ y := fun h => hxy (congrFun h m)
        have hfirst : binaryFirstDisagreement x y ≤ m := by
          by_contra hlt
          exact hxy (binaryFirstDisagreement_eq_before hXY (by omega))
        calc
          θ ^ binaryFirstDisagreement x z ≤
              θ ^ binaryFirstDisagreement x y :=
            pow_antitone_of_nonneg_of_le_one hθ.le hθ₁.le hfirst
          _ = binaryStreamPrefixDist θ x y := by
            rw [binaryStreamPrefixDist, if_neg hXY]
          _ ≤ max (binaryStreamPrefixDist θ x y)
              (binaryStreamPrefixDist θ y z) := le_max_left _ _
      · have hYZ : y ≠ z := fun h => hyz (congrFun h m)
        have hfirst : binaryFirstDisagreement y z ≤ m := by
          by_contra hlt
          exact hyz (binaryFirstDisagreement_eq_before hYZ (by omega))
        calc
          θ ^ binaryFirstDisagreement x z ≤
              θ ^ binaryFirstDisagreement y z :=
            pow_antitone_of_nonneg_of_le_one hθ.le hθ₁.le hfirst
          _ = binaryStreamPrefixDist θ y z := by
            rw [binaryStreamPrefixDist, if_neg hYZ]
          _ ≤ max (binaryStreamPrefixDist θ x y)
              (binaryStreamPrefixDist θ y z) := le_max_right _ _

theorem binaryWordPrefixDist_ultrametric
    {d : ℕ} {θ : ℝ} (hθ : 0 < θ) (hθ₁ : θ < 1) :
    RealUltrametricLaw (@binaryWordPrefixDist θ d) := by
  let hstream := binaryStreamPrefixDist_ultrametric hθ hθ₁
  refine ⟨binaryWordPrefixDist_nonneg hθ.le, ?_, ?_, ?_⟩
  · intro z w
    rw [binaryWordPrefixDist, hstream.eq_zero_iff]
    constructor
    · intro h
      simpa using congrArg (binaryPrefix d) h
    · rintro rfl
      rfl
  · intro z w
    exact hstream.symm _ _
  · intro z w u
    exact hstream.strong_triangle _ _ _

theorem binaryWordDiscreteDist_ultrametric (d : ℕ) :
    RealUltrametricLaw (@binaryWordDiscreteDist d) where
  nonneg := by
    intro z w
    simp only [binaryWordDiscreteDist]
    split <;> norm_num
  eq_zero_iff := by
    intro z w
    by_cases hzw : z = w <;> simp [binaryWordDiscreteDist, hzw]
  symm := by
    intro z w
    by_cases hzw : z = w
    · subst w; rfl
    · simp [binaryWordDiscreteDist, hzw, Ne.symm hzw]
  strong_triangle := by
    intro z w u
    by_cases hzu : z = u
    · subst u
      rw [binaryWordDiscreteDist, if_pos rfl]
      have hnonneg : 0 ≤ binaryWordDiscreteDist w z := by
        simp only [binaryWordDiscreteDist]
        split <;> norm_num
      exact hnonneg.trans (le_max_right _ _)
    · have hor : z ≠ w ∨ w ≠ u := by
        by_contra h
        simp only [not_or, not_not] at h
        exact hzu (h.1.trans h.2)
      rcases hor with hzw | hwu
      · simp [binaryWordDiscreteDist, hzu, hzw]
      · simp [binaryWordDiscreteDist, hzu, hwu]

theorem binaryPrefix_ne_firstDisagreement_lt
    {d : ℕ} {x y : BinaryStream} (hne : binaryPrefix d x ≠ binaryPrefix d y) :
    binaryFirstDisagreement x y < d := by
  have hxy : x ≠ y := fun h => hne (congrArg (binaryPrefix d) h)
  by_contra hnot
  have heq : binaryPrefix d x = binaryPrefix d y := by
    funext i
    exact binaryFirstDisagreement_eq_before hxy (by omega)
  exact hne heq

theorem binaryFirstDisagreement_extend_prefix_eq
    {d : ℕ} {x y : BinaryStream} (hne : binaryPrefix d x ≠ binaryPrefix d y) :
    binaryFirstDisagreement (binaryExtend d (binaryPrefix d x))
        (binaryExtend d (binaryPrefix d y)) =
      binaryFirstDisagreement x y := by
  let m := binaryFirstDisagreement x y
  have hm : m < d := binaryPrefix_ne_firstDisagreement_lt hne
  apply binaryFirstDisagreement_eq_of_ne_of_eq_before
  · simp [binaryExtend, hm, m]
    exact binaryFirstDisagreement_apply_ne
      (fun h => hne (congrArg (binaryPrefix d) h))
  · intro k hk
    have hkd : k < d := lt_trans hk hm
    simp [binaryExtend, hkd]
    exact binaryFirstDisagreement_eq_before
      (fun h => hne (congrArg (binaryPrefix d) h)) hk

theorem binaryWordPrefixDist_prefix_eq_stream
    {θ : ℝ} {d : ℕ} {x y : BinaryStream}
    (hne : binaryPrefix d x ≠ binaryPrefix d y) :
    binaryWordPrefixDist θ (binaryPrefix d x) (binaryPrefix d y) =
      binaryStreamPrefixDist θ x y := by
  have hxy : x ≠ y := fun h => hne (congrArg (binaryPrefix d) h)
  have hext : binaryExtend d (binaryPrefix d x) ≠
      binaryExtend d (binaryPrefix d y) := by
    intro h
    exact hne (by simpa using congrArg (binaryPrefix d) h)
  simp only [binaryWordPrefixDist, binaryStreamPrefixDist, if_neg hxy, if_neg hext,
    binaryFirstDisagreement_extend_prefix_eq hne]

/-! Exact real-valued Lipschitz and pullback budgets, without division by null effects. -/

def RealLipschitzWith {A : Type*} (distA : A → A → ℝ)
    (C : ℝ) (f : A → ℝ) : Prop :=
  ∀ x y, |f x - f y| ≤ C * distA x y

def ExactRealLipschitzConstant {A : Type*} (distA : A → A → ℝ)
    (f : A → ℝ) (C : ℝ) : Prop :=
  0 ≤ C ∧ RealLipschitzWith distA C f ∧
    ∀ D, 0 ≤ D → RealLipschitzWith distA D f → C ≤ D

def RealMapLipschitzWith {A B : Type*}
    (distA : A → A → ℝ) (distB : B → B → ℝ)
    (C : ℝ) (T : A → B) : Prop :=
  ∀ x y, distB (T x) (T y) ≤ C * distA x y

def ExactRealMapLipschitzConstant {A B : Type*}
    (distA : A → A → ℝ) (distB : B → B → ℝ)
    (T : A → B) (C : ℝ) : Prop :=
  0 ≤ C ∧ RealMapLipschitzWith distA distB C T ∧
    ∀ D, 0 ≤ D → RealMapLipschitzWith distA distB D T → C ≤ D

def RealPullbackAmplificationBound {A B : Type*}
    (distA : A → A → ℝ) (distB : B → B → ℝ)
    (T : A → B) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ (f : B → ℝ) (D : ℝ), 0 ≤ D →
    RealLipschitzWith distB D f →
      RealLipschitzWith distA (C * D) (f ∘ T)

def ExactRealPullbackAmplification {A B : Type*}
    (distA : A → A → ℝ) (distB : B → B → ℝ)
    (T : A → B) (C : ℝ) : Prop :=
  RealPullbackAmplificationBound distA distB T C ∧
    ∀ D, RealPullbackAmplificationBound distA distB T D → C ≤ D

theorem realPullbackAmplificationBound_of_mapLipschitzWith
    {A B : Type*} {distA : A → A → ℝ} {distB : B → B → ℝ}
    {T : A → B} {C : ℝ} (hC : 0 ≤ C)
    (hT : RealMapLipschitzWith distA distB C T) :
    RealPullbackAmplificationBound distA distB T C := by
  refine ⟨hC, ?_⟩
  intro f D hD hf x y
  calc
    |(f ∘ T) x - (f ∘ T) y| ≤ D * distB (T x) (T y) := hf _ _
    _ ≤ D * (C * distA x y) := by
      gcongr
      exact hT x y
    _ = (C * D) * distA x y := by ring

/-- The bounded real-valued Lipschitz effects used by `(GRA.17a)`. -/
def IsBoundedRealFunction {A : Type*} (f : A → ℝ) : Prop :=
  ∃ M : ℝ, ∀ x, |f x| ≤ M

/-- A deterministic pullback budget on all bounded Lipschitz effects. -/
def MetricPullbackAmplificationBound {A B : Type*}
    [PseudoMetricSpace A] [PseudoMetricSpace B]
    (C : NNReal) (T : A → B) : Prop :=
  ∀ (f : B → ℝ), IsBoundedRealFunction f → ∀ D : NNReal,
    LipschitzWith D f → LipschitzWith (C * D) (f ∘ T)

/-- `(GRA.17a)`: for deterministic maps, admissible pullback-amplification
constants on bounded Lipschitz effects are exactly map Lipschitz constants. -/
theorem metricPullbackAmplificationBound_iff_lipschitzWith
    {A B : Type*} [PseudoMetricSpace A] [PseudoMetricSpace B]
    (C : NNReal) (T : A → B) :
    MetricPullbackAmplificationBound C T ↔ LipschitzWith C T := by
  constructor
  · intro h
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    let R : ℝ := dist (T x) (T y)
    let f : B → ℝ := fun z => min (dist z (T y)) R
    have hR : 0 ≤ R := dist_nonneg
    have hfBounded : IsBoundedRealFunction f := by
      refine ⟨R, fun z => ?_⟩
      have hf0 : 0 ≤ f z := le_min dist_nonneg hR
      rw [abs_of_nonneg hf0]
      exact min_le_right _ _
    have hfLip : LipschitzWith 1 f := by
      have hmin := (LipschitzWith.dist_left (T y)).min
        (LipschitzWith.const (α := B) R)
      simpa [f] using hmin
    have hpull := h f hfBounded 1 hfLip
    have hxy := (lipschitzWith_iff_dist_le_mul.mp hpull) x y
    simpa [f, R, Real.dist_eq, abs_of_nonneg hR] using hxy
  · intro hT f _ D hf
    simpa [mul_comm] using hf.comp hT

def binaryZeroStream : BinaryStream := fun _ => false

def binarySingleStream (n : ℕ) : BinaryStream := fun k => decide (k = n)

@[simp] theorem binarySingleStream_apply_self (n : ℕ) :
    binarySingleStream n n = true := by simp [binarySingleStream]

theorem binaryZeroStream_ne_single (n : ℕ) :
    binaryZeroStream ≠ binarySingleStream n := by
  intro h
  have := congrFun h n
  simp [binaryZeroStream] at this

theorem binaryFirstDisagreement_zero_single (n : ℕ) :
    binaryFirstDisagreement binaryZeroStream (binarySingleStream n) = n := by
  apply binaryFirstDisagreement_eq_of_ne_of_eq_before
  · simp [binaryZeroStream]
  · intro k hk
    simp [binaryZeroStream, binarySingleStream, Nat.ne_of_lt hk]

theorem binaryStreamPrefixDist_zero_single (θ : ℝ) (n : ℕ) :
    binaryStreamPrefixDist θ binaryZeroStream (binarySingleStream n) = θ ^ n := by
  simp [binaryStreamPrefixDist, binaryZeroStream_ne_single,
    binaryFirstDisagreement_zero_single]

theorem binaryPrefix_zero_single_ne (n : ℕ) :
    binaryPrefix (n + 1) binaryZeroStream ≠
      binaryPrefix (n + 1) (binarySingleStream n) := by
  intro h
  have := congrFun h ⟨n, Nat.lt_succ_self n⟩
  simp [binaryPrefix, binaryZeroStream] at this

theorem binaryWordDiscreteDist_prefix_zero_single (n : ℕ) :
    binaryWordDiscreteDist
        (binaryPrefix (n + 1) binaryZeroStream)
        (binaryPrefix (n + 1) (binarySingleStream n)) = 1 := by
  simp [binaryWordDiscreteDist, binaryPrefix_zero_single_ne]

theorem binaryWordPrefixDist_prefix_zero_single (θ : ℝ) (n : ℕ) :
    binaryWordPrefixDist θ
        (binaryPrefix (n + 1) binaryZeroStream)
        (binaryPrefix (n + 1) (binarySingleStream n)) = θ ^ n := by
  rw [binaryWordPrefixDist_prefix_eq_stream (binaryPrefix_zero_single_ne n)]
  exact binaryStreamPrefixDist_zero_single θ n

theorem inv_pow_mul_pow_ge_one_of_le
    {θ : ℝ} (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {m n : ℕ} (hmn : m ≤ n) :
    1 ≤ (θ ^ n)⁻¹ * θ ^ m := by
  rw [mul_comm, ← div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos hθ n)).2
    (by simpa using pow_antitone_of_nonneg_of_le_one hθ.le hθ₁ hmn)

def binaryLastDetector (n : ℕ) (z : BinaryWord (n + 1)) : ℝ :=
  if z (Fin.last n) then 1 else 0

theorem binaryLastDetector_zero_prefix (n : ℕ) :
    binaryLastDetector n (binaryPrefix (n + 1) binaryZeroStream) = 0 := by
  simp [binaryLastDetector, binaryPrefix, binaryZeroStream]

theorem binaryLastDetector_single_prefix (n : ℕ) :
    binaryLastDetector n (binaryPrefix (n + 1) (binarySingleStream n)) = 1 := by
  simp [binaryLastDetector, binaryPrefix, binarySingleStream]

theorem binaryLastDetector_discrete_lipschitz (n : ℕ) :
    RealLipschitzWith binaryWordDiscreteDist 1 (binaryLastDetector n) := by
  intro z w
  by_cases hzw : z = w
  · subst w
    simp [binaryWordDiscreteDist]
  · rw [binaryWordDiscreteDist, if_neg hzw, one_mul]
    simp only [binaryLastDetector]
    split <;> split <;> norm_num

theorem binaryPrefix_discrete_mapLipschitz
    {n : ℕ} {θ : ℝ} (hθ : 0 < θ) (hθ₁ : θ < 1) :
    RealMapLipschitzWith (binaryStreamPrefixDist θ) binaryWordDiscreteDist
      ((θ ^ n)⁻¹) (binaryPrefix (n + 1)) := by
  intro x y
  by_cases hp : binaryPrefix (n + 1) x = binaryPrefix (n + 1) y
  · rw [binaryWordDiscreteDist, if_pos hp]
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg hθ.le n))
      (binaryStreamPrefixDist_nonneg hθ.le x y)
  · have hxy : x ≠ y := fun h => hp (congrArg (binaryPrefix (n + 1)) h)
    rw [binaryWordDiscreteDist, if_neg hp, binaryStreamPrefixDist, if_neg hxy]
    exact inv_pow_mul_pow_ge_one_of_le hθ hθ₁.le
      (Nat.le_of_lt_succ (binaryPrefix_ne_firstDisagreement_lt hp))

theorem binaryPrefix_discrete_exactMapLipschitz
    (n : ℕ) {θ : ℝ} (hθ : 0 < θ) (hθ₁ : θ < 1) :
    ExactRealMapLipschitzConstant (binaryStreamPrefixDist θ)
      binaryWordDiscreteDist (binaryPrefix (n + 1)) ((θ ^ n)⁻¹) := by
  refine ⟨inv_nonneg.mpr (pow_nonneg hθ.le n),
    binaryPrefix_discrete_mapLipschitz hθ hθ₁, ?_⟩
  intro D hD hmap
  have hbound := hmap binaryZeroStream (binarySingleStream n)
  rw [binaryWordDiscreteDist_prefix_zero_single,
    binaryStreamPrefixDist_zero_single] at hbound
  rw [← one_div]
  exact (div_le_iff₀ (pow_pos hθ n)).2 (by simpa [mul_comm] using hbound)

theorem binaryPrefix_inherited_mapLipschitz
    (n : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) :
    RealMapLipschitzWith (binaryStreamPrefixDist θ) (binaryWordPrefixDist θ)
      1 (binaryPrefix (n + 1)) := by
  intro x y
  by_cases hp : binaryPrefix (n + 1) x = binaryPrefix (n + 1) y
  · rw [hp]
    simpa [binaryWordPrefixDist, binaryStreamPrefixDist] using
      binaryStreamPrefixDist_nonneg hθ x y
  · rw [binaryWordPrefixDist_prefix_eq_stream hp, one_mul]

theorem binaryPrefix_inherited_exactMapLipschitz
    (n : ℕ) {θ : ℝ} (hθ : 0 < θ) :
    ExactRealMapLipschitzConstant (binaryStreamPrefixDist θ)
      (binaryWordPrefixDist θ) (binaryPrefix (n + 1)) 1 := by
  refine ⟨by norm_num, binaryPrefix_inherited_mapLipschitz n hθ.le, ?_⟩
  intro D hD hmap
  have hbound := hmap binaryZeroStream (binarySingleStream n)
  rw [binaryWordPrefixDist_prefix_zero_single,
    binaryStreamPrefixDist_zero_single] at hbound
  have hp : 0 < θ ^ n := pow_pos hθ n
  nlinarith

theorem binaryLastDetector_inherited_lipschitz
    (n : ℕ) {θ : ℝ} (hθ : 0 < θ) (hθ₁ : θ < 1) :
    RealLipschitzWith (binaryWordPrefixDist θ) ((θ ^ n)⁻¹)
      (binaryLastDetector n) := by
  intro z w
  by_cases hzw : z = w
  · subst w
    rw [sub_self, abs_zero]
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg hθ.le n))
      (binaryWordPrefixDist_nonneg hθ.le z z)
  · have hext : binaryExtend (n + 1) z ≠ binaryExtend (n + 1) w := by
      intro h
      exact hzw (by simpa using congrArg (binaryPrefix (n + 1)) h)
    have hp : binaryPrefix (n + 1) (binaryExtend (n + 1) z) ≠
        binaryPrefix (n + 1) (binaryExtend (n + 1) w) := by simpa
    have hm : binaryFirstDisagreement (binaryExtend (n + 1) z)
        (binaryExtend (n + 1) w) ≤ n :=
      Nat.le_of_lt_succ (binaryPrefix_ne_firstDisagreement_lt hp)
    have hscale := inv_pow_mul_pow_ge_one_of_le hθ hθ₁.le hm
    rw [binaryWordPrefixDist, binaryStreamPrefixDist, if_neg hext]
    calc
      |binaryLastDetector n z - binaryLastDetector n w| ≤ 1 := by
        simp only [binaryLastDetector]
        split <;> split <;> norm_num
      _ ≤ (θ ^ n)⁻¹ *
          θ ^ binaryFirstDisagreement (binaryExtend (n + 1) z)
            (binaryExtend (n + 1) w) := hscale

theorem binaryLastDetector_discrete_exactLipschitz (n : ℕ) :
    ExactRealLipschitzConstant binaryWordDiscreteDist (binaryLastDetector n) 1 := by
  refine ⟨by norm_num, binaryLastDetector_discrete_lipschitz n, ?_⟩
  intro D hD hLip
  have hbound := hLip
    (binaryPrefix (n + 1) binaryZeroStream)
    (binaryPrefix (n + 1) (binarySingleStream n))
  rw [binaryLastDetector_zero_prefix, binaryLastDetector_single_prefix,
    binaryWordDiscreteDist_prefix_zero_single] at hbound
  norm_num at hbound
  exact hbound

theorem binaryLastDetector_inherited_exactLipschitz
    (n : ℕ) {θ : ℝ} (hθ : 0 < θ) (hθ₁ : θ < 1) :
    ExactRealLipschitzConstant (binaryWordPrefixDist θ) (binaryLastDetector n)
      ((θ ^ n)⁻¹) := by
  refine ⟨inv_nonneg.mpr (pow_nonneg hθ.le n),
    binaryLastDetector_inherited_lipschitz n hθ hθ₁, ?_⟩
  intro D hD hLip
  have hbound := hLip
    (binaryPrefix (n + 1) binaryZeroStream)
    (binaryPrefix (n + 1) (binarySingleStream n))
  rw [binaryLastDetector_zero_prefix, binaryLastDetector_single_prefix,
    binaryWordPrefixDist_prefix_zero_single] at hbound
  rw [← one_div]
  exact (div_le_iff₀ (pow_pos hθ n)).2 (by simpa [mul_comm] using hbound)

theorem binaryPrefix_discrete_exactPullbackAmplification
    (n : ℕ) {θ : ℝ} (hθ : 0 < θ) (hθ₁ : θ < 1) :
    ExactRealPullbackAmplification (binaryStreamPrefixDist θ)
      binaryWordDiscreteDist (binaryPrefix (n + 1)) ((θ ^ n)⁻¹) := by
  constructor
  · exact realPullbackAmplificationBound_of_mapLipschitzWith
      (inv_nonneg.mpr (pow_nonneg hθ.le n))
      (binaryPrefix_discrete_mapLipschitz hθ hθ₁)
  · intro D hD
    have hpull := hD.2 (binaryLastDetector n) 1 (by norm_num)
      (binaryLastDetector_discrete_lipschitz n)
    have hbound := hpull binaryZeroStream (binarySingleStream n)
    rw [Function.comp_apply, Function.comp_apply,
      binaryLastDetector_zero_prefix, binaryLastDetector_single_prefix,
      binaryStreamPrefixDist_zero_single] at hbound
    rw [← one_div]
    exact (div_le_iff₀ (pow_pos hθ n)).2 (by simpa [mul_comm] using hbound)

theorem binaryPrefix_inherited_exactPullbackAmplification
    (n : ℕ) {θ : ℝ} (hθ : 0 < θ) (hθ₁ : θ < 1) :
    ExactRealPullbackAmplification (binaryStreamPrefixDist θ)
      (binaryWordPrefixDist θ) (binaryPrefix (n + 1)) 1 := by
  constructor
  · exact realPullbackAmplificationBound_of_mapLipschitzWith
      (by norm_num) (binaryPrefix_inherited_mapLipschitz n hθ.le)
  · intro D hD
    have hpull := hD.2 (binaryLastDetector n) ((θ ^ n)⁻¹)
      (inv_nonneg.mpr (pow_nonneg hθ.le n))
      (binaryLastDetector_inherited_lipschitz n hθ hθ₁)
    have hbound := hpull binaryZeroStream (binarySingleStream n)
    rw [Function.comp_apply, Function.comp_apply,
      binaryLastDetector_zero_prefix, binaryLastDetector_single_prefix,
      binaryStreamPrefixDist_zero_single] at hbound
    have hp : 0 < θ ^ n := pow_pos hθ n
    have hinv : (θ ^ n)⁻¹ * θ ^ n = 1 := inv_mul_cancel₀ hp.ne'
    nlinarith

theorem binaryLastDetector_pullback_exactLipschitz
    (n : ℕ) {θ : ℝ} (hθ : 0 < θ) (hθ₁ : θ < 1) :
    ExactRealLipschitzConstant (binaryStreamPrefixDist θ)
      (binaryLastDetector n ∘ binaryPrefix (n + 1)) ((θ ^ n)⁻¹) := by
  refine ⟨inv_nonneg.mpr (pow_nonneg hθ.le n), ?_, ?_⟩
  · simpa using
      (binaryPrefix_discrete_exactPullbackAmplification n hθ hθ₁).1.2
        (binaryLastDetector n) 1 (by norm_num)
        (binaryLastDetector_discrete_lipschitz n)
  · intro D hD hLip
    have hbound := hLip binaryZeroStream (binarySingleStream n)
    rw [Function.comp_apply, Function.comp_apply,
      binaryLastDetector_zero_prefix, binaryLastDetector_single_prefix,
      binaryStreamPrefixDist_zero_single] at hbound
    rw [← one_div]
    exact (div_le_iff₀ (pow_pos hθ n)).2 (by simpa [mul_comm] using hbound)

/-- Exact endpoint-fixed transfer identity `(GRA.22)`. -/
theorem binaryPrefix_detector_transfer_budget_identity
    (n : ℕ) (θ : ℝ) :
    (θ ^ n)⁻¹ * 1 = 1 * (θ ^ n)⁻¹ := by ring

/-! A literal Bernoulli Neyman--Pearson detector with all probability hypotheses discharged. -/

def bernoulliQuarterLowerLaw : FiniteProbabilityLaw Bool where
  prob b := if b then (1 / 4 : ℝ) else 3 / 4
  nonneg := by intro b; cases b <;> norm_num
  sum_prob := by
    classical
    rw [show (Finset.univ : Finset Bool) = {false, true} by
      ext b
      cases b <;> simp]
    norm_num

def bernoulliQuarterUpperLaw : FiniteProbabilityLaw Bool where
  prob b := if b then (3 / 4 : ℝ) else 1 / 4
  nonneg := by intro b; cases b <;> norm_num
  sum_prob := by
    classical
    rw [show (Finset.univ : Finset Bool) = {false, true} by
      ext b
      cases b <;> simp]
    norm_num

@[simp] theorem bernoulliQuarterLowerLaw_false :
    bernoulliQuarterLowerLaw.prob false = 3 / 4 := rfl

@[simp] theorem bernoulliQuarterLowerLaw_true :
    bernoulliQuarterLowerLaw.prob true = 1 / 4 := rfl

@[simp] theorem bernoulliQuarterUpperLaw_false :
    bernoulliQuarterUpperLaw.prob false = 1 / 4 := rfl

@[simp] theorem bernoulliQuarterUpperLaw_true :
    bernoulliQuarterUpperLaw.prob true = 3 / 4 := rfl

/-- Lower word at the decision boundary. Pairs `false,true` are prepended,
so the two Bernoulli weights acquire the same factor `3/16`. -/
def bernoulliBoundaryLowerWord : (n : ℕ) → BinaryWord (n + 1)
  | 0 => fun _ => false
  | 1 => fun _ => false
  | n + 2 => Fin.cons false (Fin.cons true (bernoulliBoundaryLowerWord n))

/-- Upper word at the decision boundary; it differs from the lower word only
at the final coordinate. -/
def bernoulliBoundaryUpperWord : (n : ℕ) → BinaryWord (n + 1)
  | 0 => fun _ => true
  | 1 => Fin.cons false (fun _ => true)
  | n + 2 => Fin.cons false (Fin.cons true (bernoulliBoundaryUpperWord n))

theorem tensorPower_prob_finCons
    (p : FiniteProbabilityLaw Bool) (n : ℕ) (b : Bool)
    (z : BinaryWord n) :
    (p.tensorPower (n + 1)).prob (Fin.cons b z) =
      p.prob b * (p.tensorPower n).prob z := by
  rw [FiniteProbabilityLaw.tensorPower_prob,
    Fin.prod_univ_succ, FiniteProbabilityLaw.tensorPower_prob]
  rfl

theorem bernoulliBoundary_decision_crossing (n : ℕ) :
    (bernoulliQuarterUpperLaw.tensorPower (n + 1)).prob
        (bernoulliBoundaryLowerWord n) <
      (bernoulliQuarterLowerLaw.tensorPower (n + 1)).prob
        (bernoulliBoundaryLowerWord n) ∧
    (bernoulliQuarterLowerLaw.tensorPower (n + 1)).prob
        (bernoulliBoundaryUpperWord n) ≤
      (bernoulliQuarterUpperLaw.tensorPower (n + 1)).prob
        (bernoulliBoundaryUpperWord n) := by
  induction n using Nat.twoStepInduction with
  | zero =>
      norm_num [bernoulliBoundaryLowerWord, bernoulliBoundaryUpperWord,
        FiniteProbabilityLaw.tensorPower_prob, Fin.prod_univ_succ]
  | one =>
      norm_num [bernoulliBoundaryLowerWord, bernoulliBoundaryUpperWord,
        FiniteProbabilityLaw.tensorPower_prob, Fin.prod_univ_succ]
  | more n hn _hn1 =>
      simp only [bernoulliBoundaryLowerWord, bernoulliBoundaryUpperWord,
        tensorPower_prob_finCons]
      constructor
      · norm_num only [bernoulliQuarterUpperLaw_false,
          bernoulliQuarterUpperLaw_true, bernoulliQuarterLowerLaw_false,
          bernoulliQuarterLowerLaw_true]
        nlinarith [hn.1]
      · norm_num only [bernoulliQuarterUpperLaw_false,
          bernoulliQuarterUpperLaw_true, bernoulliQuarterLowerLaw_false,
          bernoulliQuarterLowerLaw_true]
        nlinarith [hn.2]

theorem bernoulliBoundary_agree_castSucc (n : ℕ) :
    ∀ k : Fin n,
      bernoulliBoundaryLowerWord n k.castSucc =
        bernoulliBoundaryUpperWord n k.castSucc := by
  induction n using Nat.twoStepInduction with
  | zero => intro k; exact Fin.elim0 k
  | one =>
      intro k
      fin_cases k
      rfl
  | more n hn _hn1 =>
      intro k
      refine Fin.cases ?_ (fun j => ?_) k
      · rfl
      · refine Fin.cases ?_ (fun i => ?_) j
        · rfl
        · simpa [bernoulliBoundaryLowerWord, bernoulliBoundaryUpperWord] using
            hn i

theorem bernoulliBoundary_agree_before_last (n : ℕ)
    (k : Fin (n + 1)) (hk : k.val < n) :
    bernoulliBoundaryLowerWord n k = bernoulliBoundaryUpperWord n k := by
  let i : Fin n := ⟨k.val, hk⟩
  have hi : i.castSucc = k := Fin.ext rfl
  rw [← hi]
  exact bernoulliBoundary_agree_castSucc n i

@[simp] theorem bernoulliBoundaryLowerWord_last (n : ℕ) :
    bernoulliBoundaryLowerWord n (Fin.last n) = false := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n hn _hn1 =>
      simpa [bernoulliBoundaryLowerWord] using hn

@[simp] theorem bernoulliBoundaryUpperWord_last (n : ℕ) :
    bernoulliBoundaryUpperWord n (Fin.last n) = true := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n hn _hn1 =>
      simpa [bernoulliBoundaryUpperWord] using hn

theorem bernoulliBoundary_words_ne (n : ℕ) :
    bernoulliBoundaryLowerWord n ≠ bernoulliBoundaryUpperWord n := by
  intro h
  have := congrFun h (Fin.last n)
  simp at this

def bernoulliQuarterNPDetector (n : ℕ) (z : BinaryWord (n + 1)) : ℝ :=
  if (bernoulliQuarterLowerLaw.tensorPower (n + 1)).prob z ≤
      (bernoulliQuarterUpperLaw.tensorPower (n + 1)).prob z then 1 else 0

theorem bernoulliQuarterNPDetector_is_decisionEvent_indicator
    (n : ℕ) (z : BinaryWord (n + 1)) :
    bernoulliQuarterNPDetector n z =
      if z ∈ FiniteProbabilityLaw.fellerDecisionEvent
          (bernoulliQuarterLowerLaw.tensorPower (n + 1))
          (bernoulliQuarterUpperLaw.tensorPower (n + 1)) then 1 else 0 := by
  simp [bernoulliQuarterNPDetector,
    FiniteProbabilityLaw.fellerDecisionEvent]

@[simp] theorem bernoulliQuarterNPDetector_boundaryLower (n : ℕ) :
    bernoulliQuarterNPDetector n (bernoulliBoundaryLowerWord n) = 0 := by
  simp [bernoulliQuarterNPDetector,
    not_le.mpr (bernoulliBoundary_decision_crossing n).1]

@[simp] theorem bernoulliQuarterNPDetector_boundaryUpper (n : ℕ) :
    bernoulliQuarterNPDetector n (bernoulliBoundaryUpperWord n) = 1 := by
  simp [bernoulliQuarterNPDetector, (bernoulliBoundary_decision_crossing n).2]

theorem binaryFirstDisagreement_extend_bernoulliBoundary (n : ℕ) :
    binaryFirstDisagreement
        (binaryExtend (n + 1) (bernoulliBoundaryLowerWord n))
        (binaryExtend (n + 1) (bernoulliBoundaryUpperWord n)) = n := by
  apply binaryFirstDisagreement_eq_of_ne_of_eq_before
  · simp only [binaryExtend, dif_pos (Nat.lt_succ_self n)]
    have hi : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = Fin.last n := Fin.ext rfl
    rw [hi]
    simp
  · intro k hk
    have hkd : k < n + 1 := Nat.lt_succ_of_lt hk
    simp only [binaryExtend, dif_pos hkd]
    exact bernoulliBoundary_agree_before_last n ⟨k, hkd⟩ hk

theorem binaryWordDiscreteDist_bernoulliBoundary (n : ℕ) :
    binaryWordDiscreteDist (bernoulliBoundaryLowerWord n)
      (bernoulliBoundaryUpperWord n) = 1 := by
  simp [binaryWordDiscreteDist, bernoulliBoundary_words_ne]

theorem binaryWordPrefixDist_bernoulliBoundary (θ : ℝ) (n : ℕ) :
    binaryWordPrefixDist θ (bernoulliBoundaryLowerWord n)
      (bernoulliBoundaryUpperWord n) = θ ^ n := by
  have hext : binaryExtend (n + 1) (bernoulliBoundaryLowerWord n) ≠
      binaryExtend (n + 1) (bernoulliBoundaryUpperWord n) := by
    intro h
    exact bernoulliBoundary_words_ne n (by
      simpa using congrArg (binaryPrefix (n + 1)) h)
  simp [binaryWordPrefixDist, binaryStreamPrefixDist, hext,
    binaryFirstDisagreement_extend_bernoulliBoundary]

theorem binaryStreamPrefixDist_extend_bernoulliBoundary (θ : ℝ) (n : ℕ) :
    binaryStreamPrefixDist θ
        (binaryExtend (n + 1) (bernoulliBoundaryLowerWord n))
        (binaryExtend (n + 1) (bernoulliBoundaryUpperWord n)) = θ ^ n := by
  exact binaryWordPrefixDist_bernoulliBoundary θ n

theorem bernoulliQuarterNPDetector_discrete_lipschitz (n : ℕ) :
    RealLipschitzWith binaryWordDiscreteDist 1
      (bernoulliQuarterNPDetector n) := by
  intro z w
  by_cases hzw : z = w
  · subst w
    simp [binaryWordDiscreteDist]
  · rw [binaryWordDiscreteDist, if_neg hzw, one_mul]
    simp only [bernoulliQuarterNPDetector]
    split <;> split <;> norm_num

theorem bernoulliQuarterNPDetector_discrete_exactLipschitz (n : ℕ) :
    ExactRealLipschitzConstant binaryWordDiscreteDist
      (bernoulliQuarterNPDetector n) 1 := by
  refine ⟨by norm_num, bernoulliQuarterNPDetector_discrete_lipschitz n, ?_⟩
  intro D hD hLip
  have hbound := hLip (bernoulliBoundaryLowerWord n)
    (bernoulliBoundaryUpperWord n)
  rw [bernoulliQuarterNPDetector_boundaryLower,
    bernoulliQuarterNPDetector_boundaryUpper,
    binaryWordDiscreteDist_bernoulliBoundary] at hbound
  norm_num at hbound
  exact hbound

theorem bernoulliQuarterNPDetector_inherited_lipschitz
    (n : ℕ) {θ : ℝ} (hθ : 0 < θ) (hθ₁ : θ < 1) :
    RealLipschitzWith (binaryWordPrefixDist θ) ((θ ^ n)⁻¹)
      (bernoulliQuarterNPDetector n) := by
  intro z w
  by_cases hzw : z = w
  · subst w
    rw [sub_self, abs_zero]
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg hθ.le n))
      (binaryWordPrefixDist_nonneg hθ.le z z)
  · have hext : binaryExtend (n + 1) z ≠ binaryExtend (n + 1) w := by
      intro h
      exact hzw (by simpa using congrArg (binaryPrefix (n + 1)) h)
    have hp : binaryPrefix (n + 1) (binaryExtend (n + 1) z) ≠
        binaryPrefix (n + 1) (binaryExtend (n + 1) w) := by simpa
    have hm : binaryFirstDisagreement (binaryExtend (n + 1) z)
        (binaryExtend (n + 1) w) ≤ n :=
      Nat.le_of_lt_succ (binaryPrefix_ne_firstDisagreement_lt hp)
    have hscale := inv_pow_mul_pow_ge_one_of_le hθ hθ₁.le hm
    rw [binaryWordPrefixDist, binaryStreamPrefixDist, if_neg hext]
    calc
      |bernoulliQuarterNPDetector n z - bernoulliQuarterNPDetector n w| ≤ 1 := by
        simp only [bernoulliQuarterNPDetector]
        split <;> split <;> norm_num
      _ ≤ (θ ^ n)⁻¹ *
          θ ^ binaryFirstDisagreement (binaryExtend (n + 1) z)
            (binaryExtend (n + 1) w) := hscale

theorem bernoulliQuarterNPDetector_inherited_exactLipschitz
    (n : ℕ) {θ : ℝ} (hθ : 0 < θ) (hθ₁ : θ < 1) :
    ExactRealLipschitzConstant (binaryWordPrefixDist θ)
      (bernoulliQuarterNPDetector n) ((θ ^ n)⁻¹) := by
  refine ⟨inv_nonneg.mpr (pow_nonneg hθ.le n),
    bernoulliQuarterNPDetector_inherited_lipschitz n hθ hθ₁, ?_⟩
  intro D hD hLip
  have hbound := hLip (bernoulliBoundaryLowerWord n)
    (bernoulliBoundaryUpperWord n)
  rw [bernoulliQuarterNPDetector_boundaryLower,
    bernoulliQuarterNPDetector_boundaryUpper,
    binaryWordPrefixDist_bernoulliBoundary] at hbound
  rw [← one_div]
  exact (div_le_iff₀ (pow_pos hθ n)).2 (by simpa [mul_comm] using hbound)

theorem bernoulliQuarterNPDetector_pullback_exactLipschitz
    (n : ℕ) {θ : ℝ} (hθ : 0 < θ) (hθ₁ : θ < 1) :
    ExactRealLipschitzConstant (binaryStreamPrefixDist θ)
      (bernoulliQuarterNPDetector n ∘ binaryPrefix (n + 1))
      ((θ ^ n)⁻¹) := by
  refine ⟨inv_nonneg.mpr (pow_nonneg hθ.le n), ?_, ?_⟩
  · simpa using
      (binaryPrefix_discrete_exactPullbackAmplification n hθ hθ₁).1.2
        (bernoulliQuarterNPDetector n) 1 (by norm_num)
        (bernoulliQuarterNPDetector_discrete_lipschitz n)
  · intro D hD hLip
    have hbound := hLip
      (binaryExtend (n + 1) (bernoulliBoundaryLowerWord n))
      (binaryExtend (n + 1) (bernoulliBoundaryUpperWord n))
    rw [Function.comp_apply, Function.comp_apply, binaryPrefix_extend,
      binaryPrefix_extend, bernoulliQuarterNPDetector_boundaryLower,
      bernoulliQuarterNPDetector_boundaryUpper,
      binaryStreamPrefixDist_extend_bernoulliBoundary] at hbound
    rw [← one_div]
    exact (div_le_iff₀ (pow_pos hθ n)).2 (by simpa [mul_comm] using hbound)

/-! Information price and route-independent localization, `(GRA.15)`--`(GRA.17)`. -/

/-- Least gauge price among admitted effects achieving contrast at least `r`. -/
def sourceGaugePrice {E : Type*} (q : EffectGauge E)
    (admitted : E → Prop) (contrast : E → ℝ) (r : ℝ) : NNReal :=
  sInf {a | ∃ e, admitted e ∧ r ≤ contrast e ∧ q e = a}

theorem sourceGaugePrice_le {E : Type*} {q : EffectGauge E}
    {admitted : E → Prop} {contrast : E → ℝ} {r : ℝ} {e : E}
    (he : admitted e) (hr : r ≤ contrast e) :
    sourceGaugePrice q admitted contrast r ≤ q e := by
  unfold sourceGaugePrice
  apply csInf_le
  · exact ⟨0, fun _ _ => bot_le⟩
  · exact ⟨e, he, hr, rfl⟩

/-- `(GRA.15)`: exact formation makes the pulled detector admissible for
source price, and the complete path budget bounds its exact source action. -/
theorem sourceGaugePrice_le_pathAction_le_budget
    {E F G : Type*} {qE : EffectGauge E} {qF : EffectGauge F}
    {qG : EffectGauge G} (K : ResolutionArrow E F qE qF)
    (L : ResolutionArrow F G qF qG) (f : G)
    (admitted : E → Prop) (contrast : E → ℝ) (r : ℝ)
    (hadmitted : admitted (K.pull (L.pull f)))
    (hcontrast : r ≤ contrast (K.pull (L.pull f))) :
    sourceGaugePrice qE admitted contrast r ≤ K.pathAction L f ∧
      K.pathAction L f ≤ K.cost * L.cost * qG f := by
  exact ⟨sourceGaugePrice_le hadmitted hcontrast, K.pathAction_le L f⟩

/-- `(GRA.16)`, source side: the literal tensor Neyman--Pearson effect is
admissible at Hellinger contrast `1 - A^d`. Its codomain already enforces
the `[0,1]` effect constraint. -/
theorem tensorDecisionEffect_sourceGaugePrice_le
    {X Y : Type*} [PseudoMetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] [Fintype Y]
    (q : EffectGauge C(X, unitInterval))
    (mu₀ mu₁ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure mu₀]
    [MeasureTheory.IsProbabilityMeasure mu₁]
    (p₀ p₁ : FiniteProbabilityLaw Y) (d : ℕ)
    (K : FiniteFellerKernel X (Fin d → Y))
    (hK₀ : ∀ y, K.pushMass mu₀ y = (p₀.tensorPower d).prob y)
    (hK₁ : ∀ y, K.pushMass mu₁ y = (p₁.tensorPower d).prob y) :
    sourceGaugePrice q (fun _ => True)
        (fun e => FiniteFellerKernel.mixingMean e mu₁ -
          FiniteFellerKernel.mixingMean e mu₀)
        (1 - p₀.fellerHellingerAffinity p₁ ^ d) ≤
      q (K.tensorDecisionEffect p₀ p₁ d) := by
  apply sourceGaugePrice_le trivial
  exact FiniteFellerKernel.one_sub_affinity_pow_le_tensorDecisionEffect_contrast
    mu₀ mu₁ p₀ p₁ d K hK₀ hK₁

/-- `(GRA.17)`: a finite nonnegative product budget localizes at one edge
or detector, with the exact geometric-mean exponent. -/
theorem exists_factor_ge_sourceGaugePrice_root
    (n : ℕ) (R : NNReal) (factor : Fin (n + 1) → NNReal)
    (hR : R ≤ ∏ i, factor i) :
    ∃ i, R ^ ((n + 1 : ℝ)⁻¹) ≤ factor i := by
  classical
  let S : Finset NNReal := Finset.univ.image factor
  have hS : S.Nonempty := by
    exact Finset.image_nonempty.mpr Finset.univ_nonempty
  let M : NNReal := S.max' hS
  have hMmem : M ∈ S := Finset.max'_mem S hS
  obtain ⟨i, _hi, hfactor⟩ := Finset.mem_image.mp hMmem
  have hall : ∀ j ∈ (Finset.univ : Finset (Fin (n + 1))), factor j ≤ factor i := by
    intro j hj
    rw [hfactor]
    exact Finset.le_max' S (factor j) (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
  have hprod : (∏ j, factor j) ≤ factor i ^ (n + 1) := by
    simpa using Finset.prod_le_pow_card Finset.univ factor (factor i) hall
  have htotal : R ≤ factor i ^ (n + 1) := hR.trans hprod
  refine ⟨i, ?_⟩
  have hinv : 0 ≤ ((n + 1 : ℝ)⁻¹) := inv_nonneg.mpr (by positivity)
  have hrpow := NNReal.rpow_le_rpow htotal hinv
  calc
    R ^ ((n + 1 : ℝ)⁻¹) ≤
        (factor i ^ (n + 1)) ^ ((n + 1 : ℝ)⁻¹) := hrpow
    _ = factor i := by
      rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul]
      have hexp : (n + 1 : ℝ) * (n + 1 : ℝ)⁻¹ = 1 := by
        exact mul_inv_cancel₀ (by positivity)
      have hcast : ((↑(n + 1) : ℝ)) = (n + 1 : ℝ) := by norm_num
      rw [hcast]
      rw [hexp, NNReal.rpow_one]

/-- Complete finite-depth detector-transfer certificate. -/
structure BernoulliPrefixDetectorTransferCertificate (n : ℕ) (θ : ℝ) : Prop where
  sourceUltrametric : RealUltrametricLaw (binaryStreamPrefixDist θ)
  discreteTargetUltrametric : RealUltrametricLaw
    (@binaryWordDiscreteDist (n + 1))
  inheritedTargetUltrametric : RealUltrametricLaw
    (@binaryWordPrefixDist θ (n + 1))
  discreteMap : ExactRealMapLipschitzConstant (binaryStreamPrefixDist θ)
    binaryWordDiscreteDist (binaryPrefix (n + 1)) ((θ ^ n)⁻¹)
  inheritedMap : ExactRealMapLipschitzConstant (binaryStreamPrefixDist θ)
    (binaryWordPrefixDist θ) (binaryPrefix (n + 1)) 1
  discretePullback : ExactRealPullbackAmplification (binaryStreamPrefixDist θ)
    binaryWordDiscreteDist (binaryPrefix (n + 1)) ((θ ^ n)⁻¹)
  inheritedPullback : ExactRealPullbackAmplification (binaryStreamPrefixDist θ)
    (binaryWordPrefixDist θ) (binaryPrefix (n + 1)) 1
  decisionIndicator : ∀ z, bernoulliQuarterNPDetector n z =
    if z ∈ FiniteProbabilityLaw.fellerDecisionEvent
        (bernoulliQuarterLowerLaw.tensorPower (n + 1))
        (bernoulliQuarterUpperLaw.tensorPower (n + 1)) then 1 else 0
  discreteDetector : ExactRealLipschitzConstant binaryWordDiscreteDist
    (bernoulliQuarterNPDetector n) 1
  inheritedDetector : ExactRealLipschitzConstant (binaryWordPrefixDist θ)
    (bernoulliQuarterNPDetector n) ((θ ^ n)⁻¹)
  sourceDetector : ExactRealLipschitzConstant (binaryStreamPrefixDist θ)
    (bernoulliQuarterNPDetector n ∘ binaryPrefix (n + 1)) ((θ ^ n)⁻¹)
  budgetIdentity : (θ ^ n)⁻¹ * 1 = 1 * (θ ^ n)⁻¹

theorem bernoulliPrefixDetectorTransferCertificate
    (n : ℕ) {θ : ℝ} (hθ : 0 < θ) (hθ₁ : θ < 1) :
    BernoulliPrefixDetectorTransferCertificate n θ where
  sourceUltrametric := binaryStreamPrefixDist_ultrametric hθ hθ₁
  discreteTargetUltrametric := binaryWordDiscreteDist_ultrametric (n + 1)
  inheritedTargetUltrametric := binaryWordPrefixDist_ultrametric hθ hθ₁
  discreteMap := binaryPrefix_discrete_exactMapLipschitz n hθ hθ₁
  inheritedMap := binaryPrefix_inherited_exactMapLipschitz n hθ
  discretePullback := binaryPrefix_discrete_exactPullbackAmplification n hθ hθ₁
  inheritedPullback := binaryPrefix_inherited_exactPullbackAmplification n hθ hθ₁
  decisionIndicator := bernoulliQuarterNPDetector_is_decisionEvent_indicator n
  discreteDetector := bernoulliQuarterNPDetector_discrete_exactLipschitz n
  inheritedDetector := bernoulliQuarterNPDetector_inherited_exactLipschitz n hθ hθ₁
  sourceDetector := bernoulliQuarterNPDetector_pullback_exactLipschitz n hθ hθ₁
  budgetIdentity := binaryPrefix_detector_transfer_budget_identity n θ

/-- Hypothesis-free literal countermodel: quarter/three-quarter Bernoulli laws
on the half-ratio prefix ultrametric, at every positive tensor depth. -/
theorem bernoulliQuarterHalfPrefix_detectorTransfer_unconditional (n : ℕ) :
    BernoulliPrefixDetectorTransferCertificate n (1 / 2 : ℝ) := by
  exact bernoulliPrefixDetectorTransferCertificate n (by norm_num) (by norm_num)

end

end GaloisForLFunctions.HTGeometry
