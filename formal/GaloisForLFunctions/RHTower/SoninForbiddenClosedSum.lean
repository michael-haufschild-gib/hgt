import GaloisForLFunctions.HTGeometry.FriedrichsClosedSum
import GaloisForLFunctions.HTGeometry.MinimalCompleteSystemChain
import GaloisForLFunctions.RHTower.SoninEulerCornerConcrete

/-!
# The time-band plus frequency-band sum is closed

Burnol, *Two complete and minimal systems associated with the zeros of the Riemann zeta function*
(arXiv:math/0203120), uses in the second proof of Prop. 4.5 and in the proof of Prop. 4.6 that

> `L²(0,a) + F₊(L²(0,a))` is closed as a subspace of `L²(0,∞)`

(a fact he established in his C. R. note [6]).  This file proves it.

The mechanism is the classical one: the Friedrichs angle between the two bands is bounded by the
norm of the alternating block `P_B P_A P_B`, which the corpus already knows to be a strict
contraction whenever the block is compact and the two bands meet only in `0`
(`norm_centralSoninAlternatingBlock_lt_one`).  A subunit Friedrichs cosine is equivalent to
closedness of the sum (`friedrichsCosine_lt_one_iff_isClosed_sup`).

## Main results

* `friedrichsCosine_le_sqrt_norm_soninAlternatingBlock` — the angle bound.
* `friedrichsCosine_lt_one_of_norm_soninAlternatingBlock_lt_one`
* `isClosed_centralPhysicalForbidden_sup_centralFourierForbidden` — Burnol's input.
-/

noncomputable section

open scoped InnerProductSpace

namespace RHTower

open GaloisForLFunctions.HTGeometry

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H] [Nontrivial H]

omit [CompleteSpace H] [Nontrivial H] in
/-- The Friedrichs cosine of two closed subspaces is at most the square root of the norm of the
alternating block `P_B P_A P_B`. -/
theorem friedrichsCosine_le_sqrt_norm_soninAlternatingBlock
    (A B : Submodule 𝕜 H) [A.HasOrthogonalProjection] [B.HasOrthogonalProjection] :
    friedrichsCosine A B ≤ Real.sqrt ‖soninAlternatingBlock A B‖ := by
  refine Real.sSup_le ?_ (Real.sqrt_nonneg _)
  rintro r ⟨u, hu, v, hv, hun, hvn, rfl⟩
  have huA : u ∈ A := hu.1
  have hvB : v ∈ B := hv.1
  have hPu : A.starProjection u = u := Submodule.starProjection_eq_self_iff.2 huA
  have hPv : B.starProjection v = v := Submodule.starProjection_eq_self_iff.2 hvB
  -- `⟪u, v⟫ = ⟪u, P_A P_B v⟫`
  have hinner : ⟪u, v⟫_𝕜 = ⟪u, A.starProjection (B.starProjection v)⟫_𝕜 := by
    rw [hPv, ← A.inner_starProjection_left_eq_right, hPu]
  -- `‖P_A P_B v‖² = re ⟪v, block v⟫ ≤ ‖block‖`
  have hblock : ‖A.starProjection (B.starProjection v)‖ ^ 2 ≤ ‖soninAlternatingBlock A B‖ := by
    have hid : A.starProjection (A.starProjection (B.starProjection v)) =
        A.starProjection (B.starProjection v) :=
      Submodule.starProjection_eq_self_iff.2 (A.starProjection_apply_mem _)
    have hexp : (‖A.starProjection (B.starProjection v)‖ : ℝ) ^ 2 =
        RCLike.re ⟪v, soninAlternatingBlock A B v⟫_𝕜 := by
      have happ : soninAlternatingBlock A B v =
          B.starProjection (A.starProjection (B.starProjection v)) := rfl
      have h1 : ⟪A.starProjection (B.starProjection v), A.starProjection (B.starProjection v)⟫_𝕜
          = ⟪v, soninAlternatingBlock A B v⟫_𝕜 := by
        rw [happ, A.inner_starProjection_left_eq_right, hid,
          B.inner_starProjection_left_eq_right]
      rw [← h1, inner_self_eq_norm_sq]
    rw [hexp]
    calc RCLike.re ⟪v, soninAlternatingBlock A B v⟫_𝕜
        ≤ ‖⟪v, soninAlternatingBlock A B v⟫_𝕜‖ := RCLike.re_le_norm _
      _ ≤ ‖v‖ * ‖soninAlternatingBlock A B v‖ := norm_inner_le_norm _ _
      _ ≤ ‖v‖ * (‖soninAlternatingBlock A B‖ * ‖v‖) := by
          gcongr
          exact (soninAlternatingBlock A B).le_opNorm v
      _ = ‖soninAlternatingBlock A B‖ := by rw [hvn]; ring
  have hle : ‖⟪u, v⟫_𝕜‖ ≤ ‖A.starProjection (B.starProjection v)‖ := by
    rw [hinner]
    calc ‖⟪u, A.starProjection (B.starProjection v)⟫_𝕜‖
        ≤ ‖u‖ * ‖A.starProjection (B.starProjection v)‖ := norm_inner_le_norm _ _
      _ = ‖A.starProjection (B.starProjection v)‖ := by rw [hun, one_mul]
  refine le_trans hle ?_
  rw [show ‖A.starProjection (B.starProjection v)‖ =
      Real.sqrt (‖A.starProjection (B.starProjection v)‖ ^ 2) by
    rw [Real.sqrt_sq (norm_nonneg _)]]
  exact Real.sqrt_le_sqrt hblock

omit [CompleteSpace H] [Nontrivial H] in
/-- A strictly contractive alternating block forces a subunit Friedrichs cosine. -/
theorem friedrichsCosine_lt_one_of_norm_soninAlternatingBlock_lt_one
    (A B : Submodule 𝕜 H) [A.HasOrthogonalProjection] [B.HasOrthogonalProjection]
    (h : ‖soninAlternatingBlock A B‖ < 1) : friedrichsCosine A B < 1 := by
  refine lt_of_le_of_lt (friedrichsCosine_le_sqrt_norm_soninAlternatingBlock A B) ?_
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_lt_sqrt (norm_nonneg _) h

/-- **The time-band plus frequency-band sum is closed** (Burnol's input to Prop. 4.5 and
Prop. 4.6): `L²(-a, a) + F(L²(-a, a))` is a closed subspace of `L²(ℝ)`. -/
theorem isClosed_centralPhysicalForbidden_sup_centralFourierForbidden (a : ℝ) (ha : 0 < a) :
    IsClosed ((centralPhysicalForbidden a ⊔ centralFourierForbidden a : Submodule ℂ SoninL2) :
      Set SoninL2) := by
  have hA : IsClosed ((centralPhysicalForbidden a : Submodule ℂ SoninL2) : Set SoninL2) :=
    isClosed_of_hasOrthogonalProjection _
  have hB : IsClosed ((centralFourierForbidden a : Submodule ℂ SoninL2) : Set SoninL2) :=
    isClosed_of_hasOrthogonalProjection _
  refine (friedrichsCosine_lt_one_iff_isClosed_sup hA hB).1 ?_
  exact friedrichsCosine_lt_one_of_norm_soninAlternatingBlock_lt_one _ _
    (norm_centralSoninAlternatingBlock_lt_one a ha)

end RHTower
