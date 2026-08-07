import GaloisForLFunctions.RHTower.HermiteEvenCarrier
import GaloisForLFunctions.HTGeometry.HermiteL2Completeness

/-!
# Closed Hermite spans in the even Fourier sectors

The complete Hermite family has dense algebraic span in `L²(ℝ)`.  Restricting by reflection
parity gives density of the even-indexed family in the even carrier.  The self-adjoint involution
`evenFourierTransform` then splits that carrier into its `+1` and `-1` eigenspaces: the step-four
families `h_(4j)` and `h_(4j+2)` have closures exactly equal to those two sectors.

This is the completeness layer required to identify fixed prolate modes with Hermite/Fourier
sectors rather than merely exhibit finitely many trial vectors in each sector.
-/

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace RHTower

def hermiteL2Span : Submodule ℂ SoninL2 :=
  Submodule.span ℂ (Set.range hermiteL2)

theorem hermiteL2Span_orthogonal_eq_bot : Submodule.orthogonal hermiteL2Span = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro u hu
  apply GaloisForLFunctions.hermite_l2_complete
  intro n
  exact hu (hermiteL2 n) (Submodule.subset_span (Set.mem_range_self n))

theorem hermiteL2Span_topologicalClosure_eq_top :
    hermiteL2Span.topologicalClosure = ⊤ := by
  calc
    hermiteL2Span.topologicalClosure =
        Submodule.orthogonal (Submodule.orthogonal hermiteL2Span) :=
      (Submodule.orthogonal_orthogonal_eq_closure _).symm
    _ = Submodule.orthogonal (⊥ : Submodule ℂ SoninL2) := by
      rw [hermiteL2Span_orthogonal_eq_bot]
    _ = ⊤ := Submodule.bot_orthogonal_eq_top

theorem l2Reflection_hermiteL2_odd (k : ℕ) :
    l2Reflection (hermiteL2 (2 * k + 1)) = -hermiteL2 (2 * k + 1) := by
  apply Lp.ext
  have hneg := (hermiteL2_coeFn (2 * k + 1)).comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [l2Reflection_ae (hermiteL2 (2 * k + 1)), hneg,
    hermiteL2_coeFn (2 * k + 1), Lp.coeFn_neg (hermiteL2 (2 * k + 1))] with
      x href hleft hright hnegcoe
  rw [href]
  have hleft' : (hermiteL2 (2 * k + 1) : ℝ → ℂ) (-x) =
      GaloisForLFunctions.hermiteSchwartz (2 * k + 1) (-x) := by
    simpa [Function.comp_apply] using hleft
  rw [hleft', GaloisForLFunctions.hermiteSchwartz_neg, hnegcoe]
  simp only [Pi.neg_apply, hright]
  norm_num [pow_add, pow_mul]

def evenHermiteL2 (k : ℕ) : evenSubspace :=
  ⟨hermiteL2 (2 * k), hermiteL2_mem_evenSubspace k⟩

def evenHermiteL2Span : Submodule ℂ evenSubspace :=
  Submodule.span ℂ (Set.range evenHermiteL2)

theorem evenHermiteL2Span_orthogonal_eq_bot :
    Submodule.orthogonal evenHermiteL2Span = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro u hu
  apply Subtype.ext
  apply GaloisForLFunctions.hermite_l2_complete
  intro n
  rcases Nat.even_or_odd n with hn | hn
  · obtain ⟨k, rfl⟩ := hn
    change inner ℂ (hermiteL2 (k + k)) (u : SoninL2) = 0
    rw [show k + k = 2 * k by omega]
    exact hu (evenHermiteL2 k) (Submodule.subset_span (Set.mem_range_self k))
  · obtain ⟨k, rfl⟩ := hn
    change inner ℂ (hermiteL2 (2 * k + 1)) (u : SoninL2) = 0
    have href := l2Reflection_symmetric (hermiteL2 (2 * k + 1)) (u : SoninL2)
    change inner ℂ (l2Reflection (hermiteL2 (2 * k + 1))) (u : SoninL2) =
      inner ℂ (hermiteL2 (2 * k + 1)) (l2Reflection (u : SoninL2)) at href
    rw [l2Reflection_hermiteL2_odd, (mem_evenSubspace_iff (u : SoninL2)).mp u.property,
      inner_neg_left] at href
    have hz : (2 : ℂ) * inner ℂ (hermiteL2 (2 * k + 1)) (u : SoninL2) = 0 := by
      linear_combination -href
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem evenHermiteL2Span_topologicalClosure_eq_top :
    evenHermiteL2Span.topologicalClosure = ⊤ := by
  calc
    evenHermiteL2Span.topologicalClosure =
        Submodule.orthogonal (Submodule.orthogonal evenHermiteL2Span) :=
      (Submodule.orthogonal_orthogonal_eq_closure _).symm
    _ = Submodule.orthogonal (⊥ : Submodule ℂ evenSubspace) := by
      rw [evenHermiteL2Span_orthogonal_eq_bot]
    _ = ⊤ := Submodule.bot_orthogonal_eq_top

def evenFourierPositiveSubspace : Submodule ℂ evenSubspace :=
  (evenFourierTransform - 1).toLinearMap.ker

def evenFourierNegativeSubspace : Submodule ℂ evenSubspace :=
  (evenFourierTransform + 1).toLinearMap.ker

theorem mem_evenFourierPositiveSubspace_iff (f : evenSubspace) :
    f ∈ evenFourierPositiveSubspace ↔ evenFourierTransform f = f := by
  simp [evenFourierPositiveSubspace, sub_eq_zero]

theorem mem_evenFourierNegativeSubspace_iff (f : evenSubspace) :
    f ∈ evenFourierNegativeSubspace ↔ evenFourierTransform f = -f := by
  simp [evenFourierNegativeSubspace, add_eq_zero_iff_eq_neg]

theorem isClosed_evenFourierPositiveSubspace :
    IsClosed (evenFourierPositiveSubspace : Set evenSubspace) := by
  exact ContinuousLinearMap.isClosed_ker (evenFourierTransform - 1)

theorem isClosed_evenFourierNegativeSubspace :
    IsClosed (evenFourierNegativeSubspace : Set evenSubspace) := by
  exact ContinuousLinearMap.isClosed_ker (evenFourierTransform + 1)

def positiveHermiteL2Span : Submodule ℂ evenSubspace :=
  Submodule.span ℂ (Set.range hermiteEven)

def negativeHermiteL2Span : Submodule ℂ evenSubspace :=
  Submodule.span ℂ (Set.range hermiteEvenNegative)

theorem inner_negativeHermite_positiveFourier_eq_zero
    (j : ℕ) {u : evenSubspace} (hu : u ∈ evenFourierPositiveSubspace) :
    inner ℂ (hermiteEvenNegative j) u = 0 := by
  have href := evenFourierTransform_symmetric (hermiteEvenNegative j) u
  change inner ℂ (evenFourierTransform (hermiteEvenNegative j)) u =
    inner ℂ (hermiteEvenNegative j) (evenFourierTransform u) at href
  rw [evenFourierTransform_hermiteEvenNegative,
    (mem_evenFourierPositiveSubspace_iff u).mp hu, inner_neg_left] at href
  have hz : (2 : ℂ) * inner ℂ (hermiteEvenNegative j) u = 0 := by
    linear_combination -href
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem inner_positiveHermite_negativeFourier_eq_zero
    (j : ℕ) {u : evenSubspace} (hu : u ∈ evenFourierNegativeSubspace) :
    inner ℂ (hermiteEven j) u = 0 := by
  have href := evenFourierTransform_symmetric (hermiteEven j) u
  change inner ℂ (evenFourierTransform (hermiteEven j)) u =
    inner ℂ (hermiteEven j) (evenFourierTransform u) at href
  rw [evenFourierTransform_hermiteEven,
    (mem_evenFourierNegativeSubspace_iff u).mp hu, inner_neg_right] at href
  have hz : (2 : ℂ) * inner ℂ (hermiteEven j) u = 0 := by
    linear_combination href
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem positiveHermiteL2Span_orthogonal_eq_negativeSubspace :
    Submodule.orthogonal positiveHermiteL2Span = evenFourierNegativeSubspace := by
  apply le_antisymm
  · intro u hu
    rw [mem_evenFourierNegativeSubspace_iff]
    have hu' := hu
    rw [positiveHermiteL2Span, Submodule.mem_orthogonal_span_iff] at hu'
    have hsum : u + evenFourierTransform u ∈
        Submodule.orthogonal evenHermiteL2Span := by
      rw [evenHermiteL2Span, Submodule.mem_orthogonal_span_iff]
      rintro _ ⟨k, rfl⟩
      rcases Nat.even_or_odd k with hk | hk
      · obtain ⟨j, rfl⟩ := hk
        have hzero := hu' (hermiteEven j) (Set.mem_range_self j)
        have href := evenFourierTransform_symmetric (hermiteEven j) u
        change inner ℂ (evenFourierTransform (hermiteEven j)) u =
          inner ℂ (hermiteEven j) (evenFourierTransform u) at href
        rw [evenFourierTransform_hermiteEven, hzero] at href
        have htarget : inner ℂ (hermiteEven j)
            (u + evenFourierTransform u) = 0 := by
          rw [inner_add_right, hzero, ← href]
          simp
        change inner ℂ (hermiteL2 (2 * (j + j)))
          (u + evenFourierTransform u) = 0
        rw [show 2 * (j + j) = 4 * j by omega]
        exact htarget
      · obtain ⟨j, rfl⟩ := hk
        have href := evenFourierTransform_symmetric (hermiteEvenNegative j) u
        change inner ℂ (evenFourierTransform (hermiteEvenNegative j)) u =
          inner ℂ (hermiteEvenNegative j) (evenFourierTransform u) at href
        rw [evenFourierTransform_hermiteEvenNegative, inner_neg_left] at href
        have hzero : inner ℂ (hermiteEvenNegative j)
            (u + evenFourierTransform u) = 0 := by
          rw [inner_add_right, ← href]
          ring
        change inner ℂ (hermiteL2 (2 * (2 * j + 1)))
          (u + evenFourierTransform u) = 0
        rw [show 2 * (2 * j + 1) = 4 * j + 2 by omega]
        exact hzero
    rw [evenHermiteL2Span_orthogonal_eq_bot] at hsum
    have hzero : u + evenFourierTransform u = 0 := by simpa using hsum
    have hzero' : evenFourierTransform u + u = 0 := by simpa [add_comm] using hzero
    exact add_eq_zero_iff_eq_neg.mp hzero'
  · intro u hu
    rw [positiveHermiteL2Span, Submodule.mem_orthogonal_span_iff]
    rintro _ ⟨j, rfl⟩
    exact inner_positiveHermite_negativeFourier_eq_zero j hu

theorem negativeHermiteL2Span_orthogonal_eq_positiveSubspace :
    Submodule.orthogonal negativeHermiteL2Span = evenFourierPositiveSubspace := by
  apply le_antisymm
  · intro u hu
    rw [mem_evenFourierPositiveSubspace_iff]
    have hu' := hu
    rw [negativeHermiteL2Span, Submodule.mem_orthogonal_span_iff] at hu'
    have hdiff : u - evenFourierTransform u ∈
        Submodule.orthogonal evenHermiteL2Span := by
      rw [evenHermiteL2Span, Submodule.mem_orthogonal_span_iff]
      rintro _ ⟨k, rfl⟩
      rcases Nat.even_or_odd k with hk | hk
      · obtain ⟨j, rfl⟩ := hk
        have href := evenFourierTransform_symmetric (hermiteEven j) u
        change inner ℂ (evenFourierTransform (hermiteEven j)) u =
          inner ℂ (hermiteEven j) (evenFourierTransform u) at href
        rw [evenFourierTransform_hermiteEven] at href
        have hzero : inner ℂ (hermiteEven j) (u - evenFourierTransform u) = 0 := by
          rw [inner_sub_right, ← href, sub_self]
        change inner ℂ (hermiteL2 (2 * (j + j)))
          (u - evenFourierTransform u) = 0
        rw [show 2 * (j + j) = 4 * j by omega]
        exact hzero
      · obtain ⟨j, rfl⟩ := hk
        have hzero := hu' (hermiteEvenNegative j) (Set.mem_range_self j)
        have href := evenFourierTransform_symmetric (hermiteEvenNegative j) u
        change inner ℂ (evenFourierTransform (hermiteEvenNegative j)) u =
          inner ℂ (hermiteEvenNegative j) (evenFourierTransform u) at href
        rw [evenFourierTransform_hermiteEvenNegative, inner_neg_left, hzero] at href
        have hzero' : inner ℂ (hermiteEvenNegative j)
            (u - evenFourierTransform u) = 0 := by
          rw [inner_sub_right, hzero, ← href]
          simp
        change inner ℂ (hermiteL2 (2 * (2 * j + 1)))
          (u - evenFourierTransform u) = 0
        rw [show 2 * (2 * j + 1) = 4 * j + 2 by omega]
        exact hzero'
    rw [evenHermiteL2Span_orthogonal_eq_bot] at hdiff
    have hzero : u - evenFourierTransform u = 0 := by simpa using hdiff
    exact (sub_eq_zero.mp hzero).symm
  · intro u hu
    rw [negativeHermiteL2Span, Submodule.mem_orthogonal_span_iff]
    rintro _ ⟨j, rfl⟩
    exact inner_negativeHermite_positiveFourier_eq_zero j hu

theorem inner_evenFourierNegative_evenFourierPositive_eq_zero
    {v u : evenSubspace} (hv : v ∈ evenFourierNegativeSubspace)
    (hu : u ∈ evenFourierPositiveSubspace) : inner ℂ v u = 0 := by
  have href := evenFourierTransform_symmetric v u
  change inner ℂ (evenFourierTransform v) u =
    inner ℂ v (evenFourierTransform u) at href
  rw [(mem_evenFourierNegativeSubspace_iff v).mp hv,
    (mem_evenFourierPositiveSubspace_iff u).mp hu, inner_neg_left] at href
  have hz : (2 : ℂ) * inner ℂ v u = 0 := by
    linear_combination -href
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem evenFourierNegativeSubspace_orthogonal_eq_positiveSubspace :
    Submodule.orthogonal evenFourierNegativeSubspace = evenFourierPositiveSubspace := by
  apply le_antisymm
  · intro u hu
    rw [mem_evenFourierPositiveSubspace_iff]
    let v : evenSubspace := u - evenFourierTransform u
    have hv : v ∈ evenFourierNegativeSubspace := by
      rw [mem_evenFourierNegativeSubspace_iff]
      dsimp [v]
      rw [map_sub, evenFourierTransform_involutive]
      abel
    have hzero : inner ℂ v u = 0 := hu v hv
    have href := evenFourierTransform_symmetric v u
    change inner ℂ (evenFourierTransform v) u =
      inner ℂ v (evenFourierTransform u) at href
    rw [(mem_evenFourierNegativeSubspace_iff v).mp hv, inner_neg_left, hzero,
      neg_zero] at href
    have hvv : inner ℂ v v = 0 := by
      calc
        inner ℂ v v = inner ℂ v (u - evenFourierTransform u) := rfl
        _ = inner ℂ v u - inner ℂ v (evenFourierTransform u) :=
          inner_sub_right _ _ _
        _ = 0 := by rw [hzero, ← href, sub_zero]
    have hv0 : v = 0 := inner_self_eq_zero.mp hvv
    dsimp [v] at hv0
    exact (sub_eq_zero.mp hv0).symm
  · intro u hu v hv
    exact inner_evenFourierNegative_evenFourierPositive_eq_zero hv hu

theorem evenFourierPositiveSubspace_orthogonal_eq_negativeSubspace :
    Submodule.orthogonal evenFourierPositiveSubspace = evenFourierNegativeSubspace := by
  apply le_antisymm
  · intro u hu
    rw [mem_evenFourierNegativeSubspace_iff]
    let v : evenSubspace := u + evenFourierTransform u
    have hv : v ∈ evenFourierPositiveSubspace := by
      rw [mem_evenFourierPositiveSubspace_iff]
      dsimp [v]
      rw [map_add, evenFourierTransform_involutive]
      abel
    have hzero : inner ℂ v u = 0 := hu v hv
    have href := evenFourierTransform_symmetric v u
    change inner ℂ (evenFourierTransform v) u =
      inner ℂ v (evenFourierTransform u) at href
    rw [(mem_evenFourierPositiveSubspace_iff v).mp hv, hzero] at href
    have hvv : inner ℂ v v = 0 := by
      calc
        inner ℂ v v = inner ℂ v (u + evenFourierTransform u) := rfl
        _ = inner ℂ v u + inner ℂ v (evenFourierTransform u) :=
          inner_add_right _ _ _
        _ = 0 := by rw [hzero, ← href]; simp
    have hv0 : v = 0 := inner_self_eq_zero.mp hvv
    dsimp [v] at hv0
    have hzero : evenFourierTransform u + u = 0 := by
      simpa [add_comm] using hv0
    exact add_eq_zero_iff_eq_neg.mp hzero
  · intro u hu v hv
    rw [← inner_conj_symm]
    rw [inner_evenFourierNegative_evenFourierPositive_eq_zero hu hv, map_zero]

theorem positiveHermiteL2Span_topologicalClosure_eq_positiveSubspace :
    positiveHermiteL2Span.topologicalClosure = evenFourierPositiveSubspace := by
  calc
    positiveHermiteL2Span.topologicalClosure =
        Submodule.orthogonal (Submodule.orthogonal positiveHermiteL2Span) :=
      (Submodule.orthogonal_orthogonal_eq_closure _).symm
    _ = Submodule.orthogonal evenFourierNegativeSubspace := by
      rw [positiveHermiteL2Span_orthogonal_eq_negativeSubspace]
    _ = evenFourierPositiveSubspace :=
      evenFourierNegativeSubspace_orthogonal_eq_positiveSubspace

theorem negativeHermiteL2Span_topologicalClosure_eq_negativeSubspace :
    negativeHermiteL2Span.topologicalClosure = evenFourierNegativeSubspace := by
  calc
    negativeHermiteL2Span.topologicalClosure =
        Submodule.orthogonal (Submodule.orthogonal negativeHermiteL2Span) :=
      (Submodule.orthogonal_orthogonal_eq_closure _).symm
    _ = Submodule.orthogonal evenFourierPositiveSubspace := by
      rw [negativeHermiteL2Span_orthogonal_eq_positiveSubspace]
    _ = evenFourierNegativeSubspace :=
      evenFourierPositiveSubspace_orthogonal_eq_negativeSubspace

/-! ## Hilbert bases -/

/-- The normalized full Hermite family in `L²(ℝ)`. -/
def hermiteL2Unit (n : ℕ) : SoninL2 :=
  ((‖hermiteL2 n‖ : ℂ))⁻¹ • hermiteL2 n

theorem orthonormal_hermiteL2Unit : Orthonormal ℂ hermiteL2Unit := by
  constructor
  · intro n
    exact norm_smul_inv_norm
      (GaloisForLFunctions.hermiteSchwartz_toLp_ne_zero n)
  · intro i j hij
    have hzero : inner ℂ (hermiteL2 i) (hermiteL2 j) = 0 :=
      GaloisForLFunctions.inner_hermiteSchwartz_toLp_eq_zero hij
    change inner ℂ
      (((‖hermiteL2 i‖ : ℂ))⁻¹ • hermiteL2 i)
      (((‖hermiteL2 j‖ : ℂ))⁻¹ • hermiteL2 j) = 0
    rw [inner_smul_left, inner_smul_right, hzero, mul_zero, mul_zero]

theorem hermiteL2UnitSpan_orthogonal_eq_bot :
    Submodule.orthogonal (Submodule.span ℂ (Set.range hermiteL2Unit)) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro u hu
  apply GaloisForLFunctions.hermite_l2_complete
  intro n
  have hn := hu (hermiteL2Unit n)
    (Submodule.subset_span (Set.mem_range_self n))
  rw [hermiteL2Unit, inner_smul_left] at hn
  have hnormReal : ‖hermiteL2 n‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (GaloisForLFunctions.hermiteSchwartz_toLp_ne_zero n)
  have hnormComplex : ((‖hermiteL2 n‖ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hnormReal
  exact (mul_eq_zero.mp hn).resolve_left
    (star_ne_zero.mpr (inv_ne_zero hnormComplex))

/-- The normalized Hermite functions, as an unconditional Hilbert basis of `L²(ℝ)`. -/
def hermiteL2HilbertBasis : HilbertBasis ℕ ℂ SoninL2 :=
  HilbertBasis.mkOfOrthogonalEqBot orthonormal_hermiteL2Unit
    hermiteL2UnitSpan_orthogonal_eq_bot

end RHTower
