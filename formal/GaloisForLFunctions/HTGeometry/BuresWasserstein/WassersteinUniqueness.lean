import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinStrongMonotone
import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinContinuation
import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinSigmaTwo

/-!
# Global strong monotonicity and uniqueness of the Bures–Wasserstein barycentre

Local strong monotonicity of the Wasserstein vector field carries a defect linear in `‖X - Y‖`,
so on its own it separates only nearby points.  Splitting the segment from `Y` to `X` into `N`
equal pieces and telescoping the increments of `Φ` along it replaces that defect by
`‖X - Y‖ / N`:

`⟨Φ(X) - Φ(Y), X - Y⟩ ≥ (κ - C ‖X - Y‖ / N) ‖X - Y‖²_HS`  for every `N ≥ 1`,

with `κ = α²/(2β³)`.  Since `N` is arbitrary this is genuine strong monotonicity, and a
Wasserstein point of a family in `1 + S²` is therefore unique.
-/

open scoped NNReal Ring BigOperators
open ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

open GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [PartialOrder (E →L[ℂ] E)] [StarOrderedRing (E →L[ℂ] E)]
variable {ι : Type*} {s : Finset ι} {w : ι → ℝ} {Av : ι → E →L[ℂ] E}

/-! ### The segment from `Y` to `X` -/

/-- The point `Y + (k/N)(X - Y)` of the affine segment joining `Y` to `X`. -/
def segPoint (X Y : E →L[ℂ] E) (N k : ℕ) : E →L[ℂ] E :=
  Y + ((k : ℝ) / (N : ℝ)) • (X - Y)

omit [CompleteSpace E] [PartialOrder (E →L[ℂ] E)] [StarOrderedRing (E →L[ℂ] E)] in
@[simp] lemma segPoint_zero (X Y : E →L[ℂ] E) (N : ℕ) : segPoint X Y N 0 = Y := by
  simp [segPoint]

omit [CompleteSpace E] [PartialOrder (E →L[ℂ] E)] [StarOrderedRing (E →L[ℂ] E)] in
lemma segPoint_last {N : ℕ} (hN : 0 < N) (X Y : E →L[ℂ] E) : segPoint X Y N N = X := by
  have hne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [segPoint, div_self hne, one_smul]
  abel

omit [CompleteSpace E] [PartialOrder (E →L[ℂ] E)] [StarOrderedRing (E →L[ℂ] E)] in
lemma segPoint_succ_sub (X Y : E →L[ℂ] E) (N k : ℕ) :
    segPoint X Y N (k + 1) - segPoint X Y N k = ((1 : ℝ) / (N : ℝ)) • (X - Y) := by
  rw [segPoint, segPoint]
  push_cast
  rw [show ((k : ℝ) + 1) / (N : ℝ) = (k : ℝ) / (N : ℝ) + 1 / (N : ℝ) by ring, add_smul]
  abel

/-- The segment stays above `α · 1` when both endpoints do. -/
lemma smul_one_le_segPoint {X Y : E →L[ℂ] E} {α : ℝ} {N k : ℕ} (hk : k ≤ N)
    (hXα : α • (1 : E →L[ℂ] E) ≤ X) (hYα : α • (1 : E →L[ℂ] E) ≤ Y) :
    α • (1 : E →L[ℂ] E) ≤ segPoint X Y N k := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp only [Nat.le_zero] at hk
    subst hk
    simpa using hYα
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hc0 : (0 : ℝ) ≤ (k : ℝ) / (N : ℝ) := by positivity
  have hc1 : (k : ℝ) / (N : ℝ) ≤ 1 := by
    rw [div_le_one hNpos]
    exact_mod_cast hk
  have h1 : (0 : E →L[ℂ] E) ≤ (1 - (k : ℝ) / (N : ℝ)) • (Y - α • (1 : E →L[ℂ] E)) :=
    smul_nonneg (by linarith) (sub_nonneg.mpr hYα)
  have h2 : (0 : E →L[ℂ] E) ≤ ((k : ℝ) / (N : ℝ)) • (X - α • (1 : E →L[ℂ] E)) :=
    smul_nonneg hc0 (sub_nonneg.mpr hXα)
  have hid : (1 - (k : ℝ) / (N : ℝ)) • (Y - α • (1 : E →L[ℂ] E))
      + ((k : ℝ) / (N : ℝ)) • (X - α • (1 : E →L[ℂ] E))
      = segPoint X Y N k - α • (1 : E →L[ℂ] E) := by
    rw [segPoint]; module
  rw [← sub_nonneg, ← hid]
  exact add_nonneg h1 h2

/-- The segment stays below `β · 1` when both endpoints do. -/
lemma segPoint_le_smul_one {X Y : E →L[ℂ] E} {β : ℝ} {N k : ℕ} (hk : k ≤ N)
    (hXβ : X ≤ β • (1 : E →L[ℂ] E)) (hYβ : Y ≤ β • (1 : E →L[ℂ] E)) :
    segPoint X Y N k ≤ β • (1 : E →L[ℂ] E) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp only [Nat.le_zero] at hk
    subst hk
    simpa using hYβ
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hc0 : (0 : ℝ) ≤ (k : ℝ) / (N : ℝ) := by positivity
  have hc1 : (k : ℝ) / (N : ℝ) ≤ 1 := by
    rw [div_le_one hNpos]
    exact_mod_cast hk
  have h1 : (0 : E →L[ℂ] E) ≤ (1 - (k : ℝ) / (N : ℝ)) • (β • (1 : E →L[ℂ] E) - Y) :=
    smul_nonneg (by linarith) (sub_nonneg.mpr hYβ)
  have h2 : (0 : E →L[ℂ] E) ≤ ((k : ℝ) / (N : ℝ)) • (β • (1 : E →L[ℂ] E) - X) :=
    smul_nonneg hc0 (sub_nonneg.mpr hXβ)
  have hid : (1 - (k : ℝ) / (N : ℝ)) • (β • (1 : E →L[ℂ] E) - Y)
      + ((k : ℝ) / (N : ℝ)) • (β • (1 : E →L[ℂ] E) - X)
      = β • (1 : E →L[ℂ] E) - segPoint X Y N k := by
    rw [segPoint]; module
  rw [← sub_nonneg, ← hid]
  exact add_nonneg h1 h2

/-! ### Local strong monotonicity without the auxiliary unit -/

/-- **Local strong monotonicity**, with the twisted Lyapunov unit produced internally. -/
theorem re_hsInner_wassField_sub_lower' {X Y : E →L[ℂ] E} {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hX : IsStrictlyPositive X) (hY : IsStrictlyPositive Y)
    (hAα : ∀ i ∈ s, α • (1 : E →L[ℂ] E) ≤ Av i)
    (hAβ : ∀ i ∈ s, Av i ≤ β • (1 : E →L[ℂ] E))
    (hXα : α • (1 : E →L[ℂ] E) ≤ X) (hXβ : X ≤ β • (1 : E →L[ℂ] E))
    (hYα : α • (1 : E →L[ℂ] E) ≤ Y) (hYβ : Y ≤ β • (1 : E →L[ℂ] E))
    (hPHS : IsHilbertSchmidt (X - Y)) :
    (α * α / (2 * (β * (β * β))) - secondOrderConst α β * ‖X - Y‖) * hsNormSq (X - Y)
      ≤ RCLike.re (hsInner (wassField s w Av X - wassField s w Av Y) (X - Y)) := by
  classical
  have hex : ∀ i : ι, ∃ u : ((E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))ˣ, i ∈ s →
      (↑u : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
        = (lyapunov (CFC.sqrt (conjMap ((Av i) ^ (-(1/2) : ℝ)) Y⁻¹ʳ))).comp (saProj)
          + ((1 : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E)) - saProj) := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨u, hu⟩ := exists_twisted_unit (hA i hi) hY
      exact ⟨u, fun _ => hu⟩
    · exact ⟨1, fun h => absurd h hi⟩
  choose v hv using hex
  exact re_hsInner_wassField_sub_lower hα hβ hw hwsum hA hX hY hAα hAβ hXα hXβ hYα hYβ
    hPHS (hX.isSelfAdjoint.sub hY.isSelfAdjoint) hv

/-! ### Global strong monotonicity by telescoping along the segment -/

/-- **Global strong monotonicity of the Wasserstein vector field.**  Telescoping the increments
of `Φ` along the `N`-fold subdivision of the segment from `Y` to `X` divides the second-order
defect of the local estimate by `N`. -/
theorem re_hsInner_wassField_sub_lower_global {X Y : E →L[ℂ] E} {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hAα : ∀ i ∈ s, α • (1 : E →L[ℂ] E) ≤ Av i)
    (hAβ : ∀ i ∈ s, Av i ≤ β • (1 : E →L[ℂ] E))
    (hXα : α • (1 : E →L[ℂ] E) ≤ X) (hXβ : X ≤ β • (1 : E →L[ℂ] E))
    (hYα : α • (1 : E →L[ℂ] E) ≤ Y) (hYβ : Y ≤ β • (1 : E →L[ℂ] E))
    (hPHS : IsHilbertSchmidt (X - Y)) {N : ℕ} (hN : 0 < N) :
    (α * α / (2 * (β * (β * β))) - secondOrderConst α β * (‖X - Y‖ / (N : ℝ)))
        * hsNormSq (X - Y)
      ≤ RCLike.re (hsInner (wassField s w Av X - wassField s w Av Y) (X - Y)) := by
  classical
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  -- properties of the sample points
  have hseg : ∀ k : ℕ, k ≤ N →
      IsStrictlyPositive (segPoint X Y N k)
        ∧ α • (1 : E →L[ℂ] E) ≤ segPoint X Y N k
        ∧ segPoint X Y N k ≤ β • (1 : E →L[ℂ] E) := by
    intro k hk
    have h1 := smul_one_le_segPoint (α := α) hk hXα hYα
    exact ⟨isStrictlyPositive_of_smul_one_le hα h1, h1, segPoint_le_smul_one hk hXβ hYβ⟩
  have hdiff : ∀ k : ℕ, segPoint X Y N (k + 1) - segPoint X Y N k
      = ((1 : ℝ) / (N : ℝ)) • (X - Y) := fun k => segPoint_succ_sub X Y N k
  have hdiffHS : ∀ k : ℕ, IsHilbertSchmidt (segPoint X Y N (k + 1) - segPoint X Y N k) := by
    intro k
    rw [hdiff k]
    exact hPHS.real_smul _
  -- the increments of the field are Hilbert–Schmidt
  have hstepHS : ∀ k ∈ Finset.range N,
      IsHilbertSchmidt (wassField s w Av (segPoint X Y N (k + 1))
        - wassField s w Av (segPoint X Y N k)) := by
    intro k hk
    rw [Finset.mem_range] at hk
    obtain ⟨hp1, -, hb1⟩ := hseg (k + 1) hk
    obtain ⟨hp0, -, hb0⟩ := hseg k (Nat.le_of_lt hk)
    exact isHilbertSchmidt_wassField_sub hα hβ hA hp1 hp0 hAα hAβ hb1 hb0 (hdiffHS k)
  -- telescoping
  have htel : wassField s w Av X - wassField s w Av Y
      = ∑ k ∈ Finset.range N, (wassField s w Av (segPoint X Y N (k + 1))
          - wassField s w Av (segPoint X Y N k)) := by
    rw [Finset.sum_range_sub (fun k => wassField s w Av (segPoint X Y N k)) N,
      segPoint_zero, segPoint_last hN]
  rw [htel, hsInner_sum_left _ hstepHS hPHS, map_sum]
  -- the per-step estimate
  have hkey : ∀ k ∈ Finset.range N,
      (α * α / (2 * (β * (β * β))) - secondOrderConst α β * (‖X - Y‖ / (N : ℝ)))
          * hsNormSq (X - Y) / (N : ℝ)
        ≤ RCLike.re (hsInner (wassField s w Av (segPoint X Y N (k + 1))
            - wassField s w Av (segPoint X Y N k)) (X - Y)) := by
    intro k hk
    rw [Finset.mem_range] at hk
    obtain ⟨hp1, ha1, hb1⟩ := hseg (k + 1) hk
    obtain ⟨hp0, ha0, hb0⟩ := hseg k (Nat.le_of_lt hk)
    have hlocal := re_hsInner_wassField_sub_lower' (w := w) (Av := Av) hα hβ hw hwsum hA
      hp1 hp0 hAα hAβ ha1 hb1 ha0 hb0 (hdiffHS k)
    -- rewrite the increment
    rw [hdiff k] at hlocal
    -- `X - Y = N • ((1/N) • (X - Y))`
    have hscale : X - Y = (N : ℝ) • (((1 : ℝ) / (N : ℝ)) • (X - Y)) := by
      rw [smul_smul, mul_one_div, div_self hNne, one_smul]
    have hinner : RCLike.re (hsInner (wassField s w Av (segPoint X Y N (k + 1))
          - wassField s w Av (segPoint X Y N k)) (X - Y))
        = (N : ℝ) * RCLike.re (hsInner (wassField s w Av (segPoint X Y N (k + 1))
          - wassField s w Av (segPoint X Y N k)) (((1 : ℝ) / (N : ℝ)) • (X - Y))) := by
      conv_lhs => rw [hscale]
      rw [hsInner_real_smul_right]
      simp
    rw [hinner]
    -- the norms of the scaled increment
    have hnorm : ‖((1 : ℝ) / (N : ℝ)) • (X - Y)‖ = ‖X - Y‖ / (N : ℝ) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      ring
    have hsq : hsNormSq (((1 : ℝ) / (N : ℝ)) • (X - Y))
        = ((1 : ℝ) / (N : ℝ)) ^ 2 * hsNormSq (X - Y) := by
      rw [← sq_hsNorm, hsNorm_real_smul, ← sq_hsNorm, mul_pow, sq_abs]
    rw [hnorm, hsq] at hlocal
    have hgoal : (α * α / (2 * (β * (β * β)))
          - secondOrderConst α β * (‖X - Y‖ / (N : ℝ))) * hsNormSq (X - Y) / (N : ℝ)
        = (N : ℝ) * ((α * α / (2 * (β * (β * β)))
          - secondOrderConst α β * (‖X - Y‖ / (N : ℝ)))
            * (((1 : ℝ) / (N : ℝ)) ^ 2 * hsNormSq (X - Y))) := by
      field_simp
    rw [hgoal]
    exact mul_le_mul_of_nonneg_left hlocal hNpos.le
  refine le_trans ?_ (Finset.sum_le_sum hkey)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [mul_div_cancel₀ _ hNne]

/-! ### Uniqueness -/

/-- **Uniqueness of the Bures–Wasserstein barycentre in `1 + S²`.**  Two Wasserstein points of
the same family whose difference is Hilbert–Schmidt coincide. -/
theorem eq_of_isWassersteinPoint {X Y : E →L[ℂ] E} {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (hw : ∀ i ∈ s, 0 < w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hAα : ∀ i ∈ s, α • (1 : E →L[ℂ] E) ≤ Av i)
    (hAβ : ∀ i ∈ s, Av i ≤ β • (1 : E →L[ℂ] E))
    (hPHS : IsHilbertSchmidt (X - Y))
    (hXW : IsWassersteinPoint s w Av X) (hYW : IsWassersteinPoint s w Av Y) :
    X = Y := by
  classical
  obtain ⟨hXα, hXβ⟩ := IsWassersteinPoint.mem_Icc hα hβ hwsum hw hA hAα hAβ hXW
  obtain ⟨hYα, hYβ⟩ := IsWassersteinPoint.mem_Icc hα hβ hwsum hw hA hAα hAβ hYW
  have hΦX : wassField s w Av X = 0 := wassField_eq_zero_of_isWassersteinPoint hwsum hXW
  have hΦY : wassField s w Av Y = 0 := wassField_eq_zero_of_isWassersteinPoint hwsum hYW
  have hκ : (0 : ℝ) < α * α / (2 * (β * (β * β))) := by positivity
  -- choose a subdivision fine enough to beat the second-order defect
  obtain ⟨N, hNge⟩ := exists_nat_ge
    (secondOrderConst α β * ‖X - Y‖ / (α * α / (2 * (β * (β * β)))) + 1)
  have hC0 : (0 : ℝ) ≤ secondOrderConst α β * ‖X - Y‖ := by
    have := (secondOrderConst_pos hα hβ).le
    positivity
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have : (0 : ℝ) ≤ secondOrderConst α β * ‖X - Y‖ / (α * α / (2 * (β * (β * β)))) := by
      positivity
    linarith
  have hNpos : (0 : ℕ) < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; norm_num at hN1
    · exact h
  have hNR : (0 : ℝ) < (N : ℝ) := by linarith
  have hdefect : secondOrderConst α β * (‖X - Y‖ / (N : ℝ))
      < α * α / (2 * (β * (β * β))) := by
    rw [mul_div_assoc', div_lt_iff₀ hNR]
    have h1 : secondOrderConst α β * ‖X - Y‖ / (α * α / (2 * (β * (β * β)))) + 1 ≤ (N : ℝ) :=
      hNge
    have h2 : secondOrderConst α β * ‖X - Y‖ / (α * α / (2 * (β * (β * β))))
        ≤ (N : ℝ) - 1 := by linarith
    have h3 : secondOrderConst α β * ‖X - Y‖ ≤ ((N : ℝ) - 1) * (α * α / (2 * (β * (β * β)))) := by
      rw [div_le_iff₀ hκ] at h2
      exact h2
    nlinarith [hκ]
  have hmono := re_hsInner_wassField_sub_lower_global (w := w) (Av := Av) hα hβ
    (fun i hi => (hw i hi).le) hwsum hA hAα hAβ hXα hXβ hYα hYβ hPHS hNpos
  have hz : hsInner (0 : E →L[ℂ] E) (X - Y) = 0 := by
    show ∑' i, inner ℂ ((0 : E →L[ℂ] E) (hsBasis ℂ E i)) ((X - Y) (hsBasis ℂ E i)) = 0
    simp
  rw [hΦX, hΦY, sub_zero, hz] at hmono
  simp only [map_zero] at hmono
  have hnn : (0 : ℝ) ≤ hsNormSq (X - Y) := hsNormSq_nonneg _
  have hzero : hsNormSq (X - Y) = 0 := by
    by_contra hcon
    have hpos : (0 : ℝ) < hsNormSq (X - Y) := lt_of_le_of_ne hnn (Ne.symm hcon)
    nlinarith [hmono, hdefect, hpos]
  have := (hsNormSq_eq_zero_iff hPHS).mp hzero
  exact sub_eq_zero.mp this

/-! ### The barycentre of a Hilbert–Schmidt family -/

/-- **Theorem 3.12 (Kim–Mer–Pálfia).**  Let `A₁, …, A_m` be strictly positive operators with
`A_i - 1` Hilbert–Schmidt and Loewner bounds `a₀ · 1 ≤ A_i ≤ b₀ · 1` where `0 < a₀ ≤ 1 ≤ b₀`.
Then the Wasserstein equation `∑ wᵢ (Aᵢ # X⁻¹) = 1` has exactly one strictly positive solution.
Existence comes from the homotopy continuation, and uniqueness from the regularity theorem —
which puts *every* solution in `1 + S²` — together with global strong monotonicity there. -/
theorem existsUnique_isWassersteinPoint_of_sigmaTwo {a₀ b₀ : ℝ}
    (ha₀ : 0 < a₀) (ha₁ : a₀ ≤ 1) (hb₁ : 1 ≤ b₀)
    (hw : ∀ i ∈ s, 0 < w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hAα : ∀ i ∈ s, a₀ • (1 : E →L[ℂ] E) ≤ Av i)
    (hAβ : ∀ i ∈ s, Av i ≤ b₀ • (1 : E →L[ℂ] E))
    (hAHS : ∀ i ∈ s, IsHilbertSchmidt (Av i - 1)) :
    ∃! X : E →L[ℂ] E, IsWassersteinPoint s w Av X := by
  have hb₀ : (0 : ℝ) < b₀ := lt_of_lt_of_le one_pos hb₁
  obtain ⟨X, hXHS, hXW⟩ :=
    exists_isWassersteinPoint_of_Icc ha₀ ha₁ hb₁ hw hwsum hA hAα hAβ hAHS
  refine ⟨X, hXW, fun Y hYW => ?_⟩
  obtain ⟨hYα, -⟩ := IsWassersteinPoint.mem_Icc ha₀ hb₀ hwsum hw hA hAα hAβ hYW
  have hYHS : IsHilbertSchmidt (Y - 1) :=
    isHilbertSchmidt_sub_one_of_isWassersteinPoint ha₀ hwsum hA hAα hYα hAHS hYW
  have hdiff : IsHilbertSchmidt (Y - X) := by
    have hid : Y - X = (Y - 1) - (X - 1) := by abel
    rw [hid]
    exact hYHS.sub hXHS
  exact eq_of_isWassersteinPoint ha₀ hb₀ hw hwsum hA hAα hAβ hdiff hYW hXW

/-- The Hilbert–Schmidt regularity of the unique solution of Theorem 3.12. -/
theorem exists_isWassersteinPoint_sigmaTwo {a₀ b₀ : ℝ}
    (ha₀ : 0 < a₀) (ha₁ : a₀ ≤ 1) (hb₁ : 1 ≤ b₀)
    (hw : ∀ i ∈ s, 0 < w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hAα : ∀ i ∈ s, a₀ • (1 : E →L[ℂ] E) ≤ Av i)
    (hAβ : ∀ i ∈ s, Av i ≤ b₀ • (1 : E →L[ℂ] E))
    (hAHS : ∀ i ∈ s, IsHilbertSchmidt (Av i - 1)) :
    ∃! X : E →L[ℂ] E, IsHilbertSchmidt (X - 1) ∧ IsWassersteinPoint s w Av X := by
  have hb₀ : (0 : ℝ) < b₀ := lt_of_lt_of_le one_pos hb₁
  obtain ⟨X, hXW, huniq⟩ :=
    existsUnique_isWassersteinPoint_of_sigmaTwo ha₀ ha₁ hb₁ hw hwsum hA hAα hAβ hAHS
  obtain ⟨hXα, -⟩ := IsWassersteinPoint.mem_Icc ha₀ hb₀ hwsum hw hA hAα hAβ hXW
  refine ⟨X, ⟨isHilbertSchmidt_sub_one_of_isWassersteinPoint ha₀ hwsum hA hAα hXα hAHS hXW,
    hXW⟩, fun Y hY => huniq Y hY.2⟩

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
