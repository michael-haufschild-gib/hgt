/-
The true moment function and a method's upper bounds have different asymptotic slopes.

Write `m(A)` for the true moment exponent, `∫_0^T |ζ(1/2+it)|^A dt ≍ T^(m(A))`, and `M(A)` for an
upper bound produced by some method, so `m(A) ≤ M(A)`.  The slope identity applies to `m`:

    **lim m(A)/A = μ(1/2)** ,

but it does **not** apply to `M`.  A method's bounds converge to their own limit

    **s_method := lim M(A)/A  ≥  μ(1/2)** ,

with equality only if the method is asymptotically optimal.  A limit strictly above `μ(1/2)` is
precisely what "the method has a floor" means, and the campaign has established such floors for the
covering architecture and for the exponent-pair region.

This distinction retracts the previous file's reading.  The extrapolation of the four published
ratios `M(12)/12, …, M(15)/15` to a limit near `0.15696` is an extrapolation of a **method's** bounds,
not of the true moments, and is therefore *not* contradicted by `μ(1/2) ≤ 13/84`.  The published trend
is consistent, and the original conclusion — that the exponent-pair moment method approaches `13/84`
from above without reaching it — stands.

What survives, and is new, is the criterion: a moment method is asymptotically optimal exactly when
its ratios converge to `μ(1/2)`.  On the extrapolation the exponent-pair method is not, and it has
`1383/350000 ≈ 0.00395` of room left in the ratio.
-/
import GaloisForLFunctions.HTGeometry.MomentOrderTarget

namespace HTGeometry

/-! ### The two slopes -/

/-- A method's moment bounds, together with the true exponent they dominate. -/
structure MomentMethod where
  /-- The method's upper bounds. -/
  M : ℚ → ℚ
  /-- The true moment exponent. -/
  m : ℚ → ℚ
  /-- The method is an upper bound. -/
  dominates : ∀ A : ℚ, m A ≤ M A
  /-- The subconvexity exponent. -/
  mu : ℚ
  /-- The true ratios come arbitrarily close to `μ` from above. -/
  trueSaturation : ∀ ε : ℚ, 0 < ε → ∃ A : ℚ, 0 < A ∧ m A / A ≤ mu + ε
  /-- Neutrality applies to the method's bounds as well. -/
  neutrality : ∀ A : ℚ, 0 < A → mu ≤ M A / A

namespace MomentMethod

variable (P : MomentMethod)

/-- **The method's ratios dominate the true ones at every order.** -/
theorem ratio_dominates {A : ℚ} (hA : 0 < A) : P.m A / A ≤ P.M A / A := by
  apply div_le_div_of_nonneg_right' (P.dominates A) hA
where
  div_le_div_of_nonneg_right' {a b c : ℚ} (hab : a ≤ b) (hc : 0 < c) : a / c ≤ b / c := by
    rw [div_le_div_iff_of_pos_right hc]; exact hab

/-- **Every method bound is an upper bound for `μ`.** -/
theorem mu_le_method {A : ℚ} (hA : 0 < A) : P.mu ≤ P.M A / A := P.neutrality A hA

/-- **The true ratios reach any margin above `μ`; nothing forces the method's to.** -/
theorem true_ratios_reach {ε : ℚ} (hε : 0 < ε) :
    ∃ A : ℚ, 0 < A ∧ P.m A / A ≤ P.mu + ε := P.trueSaturation ε hε

/-- **A method whose ratios stay above `μ + ε` at every order has a floor**, and this is consistent:
it says nothing false about the true moments. -/
theorem method_floor_consistent {ε : ℚ} (hε : 0 < ε)
    (hfloor : ∀ A : ℚ, 0 < A → P.mu + ε ≤ P.M A / A) :
    ∃ A : ℚ, 0 < A ∧ P.m A / A ≤ P.mu + ε ∧ P.mu + ε ≤ P.M A / A := by
  obtain ⟨A, hA, hle⟩ := P.trueSaturation ε hε
  exact ⟨A, hA, hle, hfloor A hA⟩

/-- **Asymptotic optimality is the equality of the two slopes**, stated as: the method's ratios also
reach every margin above `μ`. -/
def AsymptoticallyOptimal : Prop :=
  ∀ ε : ℚ, 0 < ε → ∃ A : ℚ, 0 < A ∧ P.M A / A ≤ P.mu + ε

/-- **A method with a floor above `μ` is not asymptotically optimal.** -/
theorem floor_implies_not_optimal {ε : ℚ} (hε : 0 < ε)
    (hfloor : ∀ A : ℚ, 0 < A → P.mu + ε < P.M A / A) : ¬ P.AsymptoticallyOptimal := by
  intro hopt
  obtain ⟨A, hA, hle⟩ := hopt ε hε
  exact absurd (hfloor A hA) (not_lt.mpr hle)

end MomentMethod

/-! ### The exponent-pair moment method -/

/-- The extrapolated floor of the published method. -/
def methodFloor : ℚ := extrapolatedLimit

/-- **It lies strictly above the record**, hence strictly above `μ(1/2)`. -/
theorem methodFloor_above_record : bourgainTheta < methodFloor :=
  extrapolatedLimit_above_record

/-- **The room the method still has, in the ratio.** -/
theorem method_room : bestPublishedRatio - methodFloor = 1383 / 350000 := by
  unfold methodFloor extrapolatedLimit bestPublishedRatio bourgainTheta; norm_num

/-- It is positive and under four thousandths. -/
theorem method_room_bracket :
    0 < bestPublishedRatio - methodFloor ∧ bestPublishedRatio - methodFloor < 4 / 1000 := by
  rw [method_room]
  constructor <;> norm_num

/-- **And the floor exceeds the record by `22/10000`**, so the method cannot reach `13/84`. -/
theorem floor_exceeds_record : methodFloor - bourgainTheta = 22 / 10000 := by
  unfold methodFloor extrapolatedLimit; ring

/-- **The three quantities in order**: record, method floor, best published ratio. -/
theorem ordering :
    bourgainTheta < methodFloor ∧ methodFloor < bestPublishedRatio := by
  refine ⟨methodFloor_above_record, ?_⟩
  have := method_room
  linarith

/-- **The moment-side floor, alongside the architecture's.**  The exponent-pair moment method's floor
`≈ 0.15698` sits above the record `13/84 ≈ 0.15476`, just as the covering architecture's floor
`277/1792 ≈ 0.15458` sits below it: the two methods bracket the record from opposite sides. -/
theorem floors_bracket_record :
    spacingCoverageFloor bourgainB bourgainC < bourgainTheta ∧ bourgainTheta < methodFloor := by
  exact ⟨bourgain_floor_lt_record, methodFloor_above_record⟩

end HTGeometry
