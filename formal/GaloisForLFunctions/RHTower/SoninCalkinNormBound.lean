/-
Essential norms and compact-congruence upper bounds on a complex Hilbert space.

`essentialNorm T` is the distance from a bounded operator `T` to the compact operators. The
lower half of an exact essential-norm identity is a bound `c ≤ ‖T - K‖` against every compact
`K`; this module supplies the matching upper half from a compact congruence: if `T† T` agrees
modulo compact operators with a self-adjoint operator that is idempotent modulo compact
operators, then `T` lies within distance `1 + ε` of a compact operator for every positive `ε`.

No Calkin quotient and no spectral theory enter. The image of the unit ball under each compact
defect operator admits a finite `ε`-net; the orthogonal projection onto the span of the net
cuts the defect uniformly small, and a vector-level quadratic inequality bounds the cut
operator by `1 + ε`. The same finite-rank cut shows that an operator whose adjoint square is
compact is itself compact, which upgrades the initial-projection congruence of a Calkin
partial isometry to the final-projection congruence.

The essential norm is invariant under conjugation by a unitary and scales by the absolute
value under scalar multiplication, so exact essential norms transport from a dilation model
to its scalar multiples and unitary images.
-/
import GaloisForLFunctions.RHTower.SoninEulerCalkinPartialIsometry

noncomputable section

namespace RHTower

open ContinuousLinearMap Metric
open scoped InnerProduct

/-! ### The essential norm -/

section EssentialNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The essential norm of a bounded operator: its distance from the compact operators. -/
def essentialNorm (T : E →L[ℂ] E) : ℝ :=
  sInf {r : ℝ | ∃ K : E →L[ℂ] E, IsCompactOperator K ∧ ‖T - K‖ = r}

theorem essentialNorm_set_nonempty (T : E →L[ℂ] E) :
    {r : ℝ | ∃ K : E →L[ℂ] E, IsCompactOperator K ∧ ‖T - K‖ = r}.Nonempty :=
  ⟨‖T‖, 0, isCompactOperator_zero, by rw [sub_zero]⟩

theorem essentialNorm_set_bddBelow (T : E →L[ℂ] E) :
    BddBelow {r : ℝ | ∃ K : E →L[ℂ] E, IsCompactOperator K ∧ ‖T - K‖ = r} := by
  refine ⟨0, ?_⟩
  rintro r ⟨K, _, rfl⟩
  positivity

/-- Every compact perturbation bounds the essential norm from above. -/
theorem essentialNorm_le (T K : E →L[ℂ] E) (hK : IsCompactOperator K) :
    essentialNorm T ≤ ‖T - K‖ :=
  csInf_le (essentialNorm_set_bddBelow T) ⟨K, hK, rfl⟩

/-- A uniform lower bound against every compact perturbation bounds the essential norm from
below. -/
theorem le_essentialNorm (T : E →L[ℂ] E) (c : ℝ)
    (h : ∀ K : E →L[ℂ] E, IsCompactOperator K → c ≤ ‖T - K‖) :
    c ≤ essentialNorm T := by
  refine le_csInf (essentialNorm_set_nonempty T) ?_
  rintro r ⟨K, hK, rfl⟩
  exact h K hK

theorem essentialNorm_nonneg (T : E →L[ℂ] E) : 0 ≤ essentialNorm T :=
  le_essentialNorm T 0 fun _ _ => norm_nonneg _

/-- Near-optimal compact perturbations at every positive tolerance bound the essential norm
from above. -/
theorem essentialNorm_le_of_forall_exists (T : E →L[ℂ] E) (c : ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ K : E →L[ℂ] E, IsCompactOperator K ∧ ‖T - K‖ ≤ c + ε) :
    essentialNorm T ≤ c := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨K, hK, hle⟩ := h ε hε
  exact (essentialNorm_le T K hK).trans hle

/-- The exact essential norm from a matching pair of lower and upper bounds. -/
theorem essentialNorm_eq_of_bounds (T : E →L[ℂ] E) (c : ℝ)
    (hlower : ∀ K : E →L[ℂ] E, IsCompactOperator K → c ≤ ‖T - K‖)
    (hupper : ∀ ε : ℝ, 0 < ε → ∃ K : E →L[ℂ] E, IsCompactOperator K ∧ ‖T - K‖ ≤ c + ε) :
    essentialNorm T = c :=
  le_antisymm (essentialNorm_le_of_forall_exists T c hupper) (le_essentialNorm T c hlower)

theorem essentialNorm_zero : essentialNorm (0 : E →L[ℂ] E) = 0 :=
  le_antisymm (by simpa using essentialNorm_le (0 : E →L[ℂ] E) 0 isCompactOperator_zero)
    (essentialNorm_nonneg 0)

theorem essentialNorm_smul_le (c : ℂ) (T : E →L[ℂ] E) :
    essentialNorm (c • T) ≤ ‖c‖ * essentialNorm T := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [zero_smul, essentialNorm_zero, norm_zero, zero_mul]
  · have hc0 : (0 : ℝ) < ‖c‖ := norm_pos_iff.mpr hc
    apply le_of_forall_pos_le_add
    intro ε hε
    have hlt : essentialNorm T < essentialNorm T + ε / ‖c‖ :=
      lt_add_of_pos_right _ (div_pos hε hc0)
    obtain ⟨r, hrmem, hr⟩ := (csInf_lt_iff (essentialNorm_set_bddBelow T)
      (essentialNorm_set_nonempty T)).mp hlt
    obtain ⟨K, hK, rfl⟩ := hrmem
    calc essentialNorm (c • T) ≤ ‖c • T - c • K‖ := essentialNorm_le _ _ (hK.smul c)
      _ = ‖c‖ * ‖T - K‖ := by rw [← smul_sub, norm_smul]
      _ ≤ ‖c‖ * (essentialNorm T + ε / ‖c‖) := mul_le_mul_of_nonneg_left hr.le hc0.le
      _ = ‖c‖ * essentialNorm T + ε := by field_simp

/-- The essential norm scales exactly by the scalar's absolute value. -/
theorem essentialNorm_smul (c : ℂ) (T : E →L[ℂ] E) :
    essentialNorm (c • T) = ‖c‖ * essentialNorm T := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [zero_smul, essentialNorm_zero, norm_zero, zero_mul]
  · refine le_antisymm (essentialNorm_smul_le c T) ?_
    have h := essentialNorm_smul_le c⁻¹ (c • T)
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul, norm_inv] at h
    have hc0 : (0 : ℝ) < ‖c‖ := norm_pos_iff.mpr hc
    calc ‖c‖ * essentialNorm T ≤ ‖c‖ * (‖c‖⁻¹ * essentialNorm (c • T)) :=
          mul_le_mul_of_nonneg_left h hc0.le
      _ = essentialNorm (c • T) := by field_simp

end EssentialNorm

/-! ### Unitary invariance of the essential norm -/

section UnitaryTransport

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

theorem norm_unitaryPush_le (u : H ≃ₗᵢ[ℂ] K) (T : H →L[ℂ] H) :
    ‖unitaryPush u T‖ ≤ ‖T‖ := by
  apply opNorm_le_bound _ (norm_nonneg T)
  intro x
  rw [unitaryPush_apply]
  calc ‖u (T (u.symm x))‖ = ‖T (u.symm x)‖ := u.norm_map _
    _ ≤ ‖T‖ * ‖u.symm x‖ := T.le_opNorm _
    _ = ‖T‖ * ‖x‖ := by rw [u.symm.norm_map]

theorem unitaryPush_symm_unitaryPush (u : H ≃ₗᵢ[ℂ] K) (T : H →L[ℂ] H) :
    unitaryPush u.symm (unitaryPush u T) = T := by
  apply ContinuousLinearMap.ext
  intro x
  simp

/-- Conjugation by a unitary preserves the operator norm. -/
theorem norm_unitaryPush (u : H ≃ₗᵢ[ℂ] K) (T : H →L[ℂ] H) :
    ‖unitaryPush u T‖ = ‖T‖ := by
  refine le_antisymm (norm_unitaryPush_le u T) ?_
  conv_lhs => rw [← unitaryPush_symm_unitaryPush u T]
  exact norm_unitaryPush_le u.symm (unitaryPush u T)

/-- Conjugation by a unitary preserves compactness. -/
theorem isCompactOperator_unitaryPush (u : H ≃ₗᵢ[ℂ] K) {T : H →L[ℂ] H}
    (hT : IsCompactOperator T) : IsCompactOperator (unitaryPush u T) := by
  have h := (hT.comp_clm (u.symm : K →L[ℂ] H)).clm_comp (u : H →L[ℂ] K)
  simpa [unitaryPush, Function.comp_def] using h

theorem essentialNorm_unitaryPush_le (u : H ≃ₗᵢ[ℂ] K) (T : H →L[ℂ] H) :
    essentialNorm (unitaryPush u T) ≤ essentialNorm T := by
  apply csInf_le_csInf (essentialNorm_set_bddBelow (unitaryPush u T))
    (essentialNorm_set_nonempty T)
  rintro r ⟨W, hW, rfl⟩
  exact ⟨unitaryPush u W, isCompactOperator_unitaryPush u hW,
    by rw [← unitaryPush_sub, norm_unitaryPush]⟩

/-- Conjugation by a unitary preserves the essential norm. -/
theorem essentialNorm_unitaryPush (u : H ≃ₗᵢ[ℂ] K) (T : H →L[ℂ] H) :
    essentialNorm (unitaryPush u T) = essentialNorm T := by
  refine le_antisymm (essentialNorm_unitaryPush_le u T) ?_
  conv_lhs => rw [← unitaryPush_symm_unitaryPush u T]
  exact essentialNorm_unitaryPush_le u.symm (unitaryPush u T)

end UnitaryTransport

/-! ### Finite-rank orthogonal cuts of compact operators -/

section FiniteRankCut

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private theorem le_one_add_mul_of_sq_le_mul_add_sq {a b ε : ℝ} (hb : 0 ≤ b) (hε : 0 < ε)
    (h : a ^ 2 ≤ a * b + ε * b ^ 2) : a ≤ (1 + ε) * b := by
  by_contra hcon
  rw [not_le] at hcon
  have hba : b < a := by nlinarith
  have ha0 : 0 < a := hb.trans_lt hba
  have h1 : (1 + ε) * b * a < a * a := mul_lt_mul_of_pos_right hcon ha0
  have h2 : ε * (b * a) < ε * (b * b) := by nlinarith
  have h3 : b * a < b * b := lt_of_mul_lt_mul_left h2 hε.le
  have h4 : b * b ≤ b * a := mul_le_mul_of_nonneg_left hba.le hb
  exact absurd h3 (not_lt.mpr h4)

private theorem le_of_sq_le_sq {a b : ℝ} (hb : 0 ≤ b)
    (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by nlinarith

/-- The orthogonal projection onto a finite-dimensional subspace is a compact operator. -/
theorem isCompactOperator_starProjection_of_finiteDimensional
    (V : Submodule ℂ H) [FiniteDimensional ℂ V] :
    IsCompactOperator V.starProjection := by
  refine ⟨Subtype.val '' closedBall (0 : V) 1,
    (isCompact_closedBall 0 1).image continuous_subtype_val, ?_⟩
  refine Filter.mem_of_superset (Metric.ball_mem_nhds 0 one_pos) ?_
  intro x hx
  refine ⟨V.orthogonalProjection x, ?_, (V.starProjection_apply x).symm⟩
  rw [mem_closedBall_zero_iff]
  calc ‖V.orthogonalProjection x‖ = ‖V.starProjection x‖ := rfl
    _ ≤ ‖x‖ := V.norm_starProjection_apply_le x
    _ ≤ 1 := le_of_lt (mem_ball_zero_iff.mp hx)

/-- A compact operator is uniformly small after cutting by the orthogonal complement of the
span of any finite set containing an `ε`-net of the image of the unit ball. -/
theorem exists_finset_forall_norm_cut_mul_le
    {C : H →L[ℂ] H} (hC : IsCompactOperator C) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset H, ∀ t : Finset H, s ⊆ t →
      ‖(1 - (Submodule.span ℂ (t : Set H)).starProjection) * C‖ ≤ ε := by
  have htb : TotallyBounded (C '' closedBall 0 1) :=
    (hC.isCompact_closure_image_closedBall 1).totallyBounded.subset subset_closure
  obtain ⟨t₀, ht₀fin, ht₀cov⟩ := Metric.totallyBounded_iff.mp htb (ε / 2) (by positivity)
  refine ⟨ht₀fin.toFinset, fun t hst => ?_⟩
  set V := Submodule.span ℂ (t : Set H) with hV
  refine opNorm_le_of_shell (f := (1 - V.starProjection) * C) one_pos hε.le
    (c := (2 : ℂ)) (by norm_num) ?_
  intro x hx1 hx2
  have hxball : x ∈ closedBall (0 : H) 1 := by
    rw [mem_closedBall_zero_iff]
    exact hx2.le
  have hCx : C x ∈ ⋃ y ∈ t₀, ball y (ε / 2) := ht₀cov ⟨x, hxball, rfl⟩
  obtain ⟨y, hyt₀, hy⟩ := Set.mem_iUnion₂.mp hCx
  have hyV : y ∈ V := by
    apply Submodule.subset_span
    have hmem : y ∈ ht₀fin.toFinset := ht₀fin.mem_toFinset.mpr hyt₀
    exact_mod_cast hst hmem
  have hmin : ‖C x - V.starProjection (C x)‖ ≤ ‖C x - y‖ := by
    rw [Submodule.starProjection_minimal]
    exact ciInf_le ⟨0, by rintro r ⟨v, rfl⟩; positivity⟩ (⟨y, hyV⟩ : V)
  have hnormx : (1 : ℝ) / ‖(2 : ℂ)‖ = 1 / 2 := by norm_num
  calc ‖((1 - V.starProjection) * C) x‖ = ‖C x - V.starProjection (C x)‖ := by
        simp [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply]
    _ ≤ ‖C x - y‖ := hmin
    _ ≤ ε / 2 := le_of_lt (by simpa [dist_eq_norm] using hy)
    _ ≤ ε * ‖x‖ := by
        rw [hnormx] at hx1
        nlinarith

end FiniteRankCut

/-! ### The compact-congruence upper bound -/

section UpperBound

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem adjoint_one_sub {P : H →L[ℂ] H}
    (hPadj : ContinuousLinearMap.adjoint P = P) :
    ContinuousLinearMap.adjoint ((1 : H →L[ℂ] H) - P) = 1 - P := by
  have h : star ((1 : H →L[ℂ] H) - P) = 1 - P := by
    rw [star_sub, star_one]
    exact congrArg (fun W => (1 : H →L[ℂ] H) - W) hPadj
  exact h

/-- After cutting by a self-adjoint idempotent-complement, the quadratic form of an
operator with a small cut is uniformly small. -/
private theorem re_inner_apply_cut_le
    (P C : H →L[ℂ] H) (hPadj : ContinuousLinearMap.adjoint P = P)
    {ε : ℝ} (hε : 0 ≤ ε) (hC : ∀ z : H, ‖((1 - P) * C) z‖ ≤ ε * ‖z‖)
    (x : H) (hyx : ‖x - P x‖ ≤ ‖x‖) :
    (inner ℂ (C (x - P x)) (x - P x) : ℂ).re ≤ ε * ‖x‖ ^ 2 := by
  set y := x - P x with hy
  have h1subP : ((1 : H →L[ℂ] H) - P) x = x - P x := by
    simp [ContinuousLinearMap.sub_apply]
  have hswap : (inner ℂ (C y) y : ℂ) = inner ℂ (((1 : H →L[ℂ] H) - P) (C y)) x := by
    have h1 : (inner ℂ (C y) y : ℂ) = inner ℂ (C y) (((1 : H →L[ℂ] H) - P) x) := by
      rw [h1subP]
    rw [h1, ← ContinuousLinearMap.adjoint_inner_left, adjoint_one_sub hPadj]
  have habs : ‖(inner ℂ (((1 : H →L[ℂ] H) - P) (C y)) x : ℂ)‖ ≤ ε * ‖x‖ ^ 2 := by
    calc ‖(inner ℂ (((1 : H →L[ℂ] H) - P) (C y)) x : ℂ)‖ ≤
        ‖((1 : H →L[ℂ] H) - P) (C y)‖ * ‖x‖ := norm_inner_le_norm _ _
      _ = ‖((1 - P) * C) y‖ * ‖x‖ := by rw [ContinuousLinearMap.mul_apply]
      _ ≤ (ε * ‖y‖) * ‖x‖ := mul_le_mul_of_nonneg_right (hC y) (norm_nonneg x)
      _ ≤ (ε * ‖x‖) * ‖x‖ := by
          have h2 : ε * ‖y‖ ≤ ε * ‖x‖ := mul_le_mul_of_nonneg_left hyx hε
          exact mul_le_mul_of_nonneg_right h2 (norm_nonneg x)
      _ = ε * ‖x‖ ^ 2 := by ring
  rw [hswap]
  exact (Complex.re_le_norm _).trans habs

/-- **Compact-congruence upper bound.** If `T† T` agrees modulo compact operators with a
self-adjoint operator `S` that is idempotent modulo compact operators, then `T` lies within
distance `1 + ε` of a compact operator: cutting `T` by the span of a finite `ε`-net of the
two compact defects leaves an operator of norm at most `1 + ε`. -/
theorem exists_isCompactOperator_norm_sub_le_one_add
    (T S : H →L[ℂ] H) (hSadj : (S†) = S)
    (hTS : (T†) * T =ₖ S) (hSS : S * S =ₖ S)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : H →L[ℂ] H, IsCompactOperator K ∧ ‖T - K‖ ≤ 1 + ε := by
  have hC₀ : IsCompactOperator (((T†) * T - S : H →L[ℂ] H)) := hTS
  have hC₁ : IsCompactOperator ((S * S - S : H →L[ℂ] H)) := hSS
  obtain ⟨s₀, hs₀⟩ := exists_finset_forall_norm_cut_mul_le hC₀ hε
  obtain ⟨s₁, hs₁⟩ := exists_finset_forall_norm_cut_mul_le hC₁ hε
  set t : Finset H := s₀ ∪ s₁ with ht
  set V := Submodule.span ℂ (t : Set H) with hV
  have h₀ := hs₀ t Finset.subset_union_left
  have h₁ := hs₁ t Finset.subset_union_right
  set P := V.starProjection with hP
  have hPadj : ContinuousLinearMap.adjoint P = P := (isSelfAdjoint_starProjection V).star_eq
  have hcut : ∀ z : H, ‖z - P z‖ ≤ ‖z‖ := by
    intro z
    have h1 : z - P z = Vᗮ.starProjection z := by
      rw [V.starProjection_orthogonal']
      simp [ContinuousLinearMap.sub_apply]
    rw [h1]
    exact Vᗮ.norm_starProjection_apply_le z
  have h₀' : ∀ z : H, ‖((1 - P) * ((T†) * T - S)) z‖ ≤ ε * ‖z‖ := fun z =>
    (le_opNorm _ z).trans (mul_le_mul_of_nonneg_right h₀ (norm_nonneg z))
  have h₁' : ∀ z : H, ‖((1 - P) * (S * S - S)) z‖ ≤ ε * ‖z‖ := fun z =>
    (le_opNorm _ z).trans (mul_le_mul_of_nonneg_right h₁ (norm_nonneg z))
  refine ⟨T * P, (isCompactOperator_starProjection_of_finiteDimensional V).clm_comp T, ?_⟩
  apply opNorm_le_bound _ (by positivity)
  intro x
  have hTP : (T - T * P) x = T (x - P x) := by
    simp [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply, map_sub]
  rw [hTP]
  set y := x - P x with hy
  have hyx : ‖y‖ ≤ ‖x‖ := hcut x
  -- the shell factor is a near-contraction on the cut vector
  have hSy : ‖S y‖ ≤ (1 + ε) * ‖x‖ := by
    have hmove : (inner ℂ (S (S y)) y : ℂ) = inner ℂ (S y) ((S†) y) :=
      (ContinuousLinearMap.adjoint_inner_right S (S y) y).symm
    rw [hSadj] at hmove
    have hsq : ‖S y‖ ^ 2 = (inner ℂ ((S * S) y) y : ℂ).re := by
      rw [ContinuousLinearMap.mul_apply, hmove]
      exact (inner_self_eq_norm_sq (𝕜 := ℂ) (S y)).symm
    have hsplit : (inner ℂ ((S * S) y) y : ℂ).re =
        (inner ℂ (S y) y : ℂ).re + (inner ℂ ((S * S - S) y) y : ℂ).re := by
      have hdecomp : (S * S) y = S y + (S * S - S) y := by
        simp [ContinuousLinearMap.sub_apply]
      rw [hdecomp, inner_add_left, Complex.add_re]
    have hlin : (inner ℂ (S y) y : ℂ).re ≤ ‖S y‖ * ‖x‖ := by
      calc (inner ℂ (S y) y : ℂ).re ≤ ‖(inner ℂ (S y) y : ℂ)‖ := Complex.re_le_norm _
        _ ≤ ‖S y‖ * ‖y‖ := norm_inner_le_norm _ _
        _ ≤ ‖S y‖ * ‖x‖ := mul_le_mul_of_nonneg_left hyx (norm_nonneg _)
    have hquad : ‖S y‖ ^ 2 ≤ ‖S y‖ * ‖x‖ + ε * ‖x‖ ^ 2 := by
      rw [hsq, hsplit]
      exact add_le_add hlin (re_inner_apply_cut_le P _ hPadj hε.le h₁' x (hcut x))
    exact le_one_add_mul_of_sq_le_mul_add_sq (norm_nonneg _) hε hquad
  -- the corner itself obeys the same near-contraction
  have hTsq : ‖T y‖ ^ 2 = (inner ℂ (((T†) * T) y) y : ℂ).re := by
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.adjoint_inner_left]
    exact (inner_self_eq_norm_sq (𝕜 := ℂ) (T y)).symm
  have hTsplit : (inner ℂ (((T†) * T) y) y : ℂ).re =
      (inner ℂ (S y) y : ℂ).re + (inner ℂ (((T†) * T - S) y) y : ℂ).re := by
    have hdecomp : ((T†) * T) y = S y + ((T†) * T - S) y := by
      simp [ContinuousLinearMap.sub_apply]
    rw [hdecomp, inner_add_left, Complex.add_re]
  have hlin' : (inner ℂ (S y) y : ℂ).re ≤ (1 + ε) * ‖x‖ * ‖x‖ := by
    calc (inner ℂ (S y) y : ℂ).re ≤ ‖(inner ℂ (S y) y : ℂ)‖ := Complex.re_le_norm _
      _ ≤ ‖S y‖ * ‖y‖ := norm_inner_le_norm _ _
      _ ≤ ((1 + ε) * ‖x‖) * ‖x‖ := by
          apply mul_le_mul hSy hyx (norm_nonneg _)
          positivity
  have hTquad : ‖T y‖ ^ 2 ≤ (1 + ε) * ‖x‖ * ‖x‖ + ε * ‖x‖ ^ 2 := by
    rw [hTsq, hTsplit]
    exact add_le_add hlin' (re_inner_apply_cut_le P _ hPadj hε.le h₀' x (hcut x))
  have hfinal : ‖T y‖ ^ 2 ≤ ((1 + ε) * ‖x‖) ^ 2 := by
    nlinarith [norm_nonneg x, sq_nonneg ‖x‖]
  exact le_of_sq_le_sq (by positivity) hfinal

/-- If the adjoint square of an operator is compact, the operator is within any positive
distance of a compact operator. -/
theorem exists_isCompactOperator_norm_sub_le_of_adjoint_mul_isCompact
    (T : H →L[ℂ] H) (hTT : IsCompactOperator (((T†) * T : H →L[ℂ] H)))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : H →L[ℂ] H, IsCompactOperator K ∧ ‖T - K‖ ≤ δ := by
  obtain ⟨s₀, hs₀⟩ := exists_finset_forall_norm_cut_mul_le hTT (mul_pos hδ hδ)
  set V := Submodule.span ℂ ((s₀ : Finset H) : Set H) with hV
  have h₀ := hs₀ s₀ (Finset.Subset.refl s₀)
  set P := V.starProjection with hP
  have hPadj : ContinuousLinearMap.adjoint P = P := (isSelfAdjoint_starProjection V).star_eq
  have hcut : ∀ z : H, ‖z - P z‖ ≤ ‖z‖ := by
    intro z
    have h1 : z - P z = Vᗮ.starProjection z := by
      rw [V.starProjection_orthogonal']
      simp [ContinuousLinearMap.sub_apply]
    rw [h1]
    exact Vᗮ.norm_starProjection_apply_le z
  have h₀' : ∀ z : H, ‖((1 - P) * ((T†) * T)) z‖ ≤ (δ * δ) * ‖z‖ := fun z =>
    (le_opNorm _ z).trans (mul_le_mul_of_nonneg_right h₀ (norm_nonneg z))
  refine ⟨T * P, (isCompactOperator_starProjection_of_finiteDimensional V).clm_comp T, ?_⟩
  apply opNorm_le_bound _ hδ.le
  intro x
  have hTP : (T - T * P) x = T (x - P x) := by
    simp [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply, map_sub]
  rw [hTP]
  set y := x - P x with hy
  have hTsq : ‖T y‖ ^ 2 = (inner ℂ (((T†) * T) y) y : ℂ).re := by
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.adjoint_inner_left]
    exact (inner_self_eq_norm_sq (𝕜 := ℂ) (T y)).symm
  have hTquad : ‖T y‖ ^ 2 ≤ (δ * δ) * ‖x‖ ^ 2 := by
    rw [hTsq]
    exact re_inner_apply_cut_le P _ hPadj (by positivity) h₀' x (hcut x)
  have hfinal : ‖T y‖ ^ 2 ≤ (δ * ‖x‖) ^ 2 := by nlinarith
  exact le_of_sq_le_sq (by positivity) hfinal

/-- An operator whose adjoint square is compact modulo nothing is itself compact: the set of
compact operators is closed and the finite-rank cuts converge to the operator in norm. -/
theorem isCompactOperator_of_adjoint_mul_compactEq_zero
    (T : H →L[ℂ] H) (hTT : (T†) * T =ₖ 0) : IsCompactOperator T := by
  have hcpt : IsCompactOperator (((T†) * T : H →L[ℂ] H)) := by
    have h : IsCompactOperator (((T†) * T - 0 : H →L[ℂ] H)) := hTT
    simpa using h
  have hmem : T ∈ closure {W : H →L[ℂ] H | IsCompactOperator W} := by
    rw [Metric.mem_closure_iff]
    intro δ hδ
    obtain ⟨K, hK, hle⟩ :=
      exists_isCompactOperator_norm_sub_le_of_adjoint_mul_isCompact T hcpt (half_pos hδ)
    refine ⟨K, hK, ?_⟩
    rw [dist_eq_norm]
    exact hle.trans_lt (half_lt_self hδ)
  exact isClosed_setOf_isCompactOperator.closure_subset hmem

/-- A corner annihilates the complement of its initial Calkin projection modulo compact
operators. -/
theorem isCompactOperator_mul_one_sub_of_compactEq
    (L S : H →L[ℂ] H) (hSadj : (S†) = S)
    (hLS : (L†) * L =ₖ S) (hSS : S * S =ₖ S) :
    IsCompactOperator ((L * (1 - S) : H →L[ℂ] H)) := by
  apply isCompactOperator_of_adjoint_mul_compactEq_zero
  have hadj : ((L * (1 - S))†) = (1 - S) * (L†) := by
    have h : star (L * (1 - S)) = star ((1 : H →L[ℂ] H) - S) * star L := star_mul _ _
    have h1S : star ((1 : H →L[ℂ] H) - S) = 1 - S := by
      rw [star_sub, star_one]
      exact congrArg (fun W => (1 : H →L[ℂ] H) - W) hSadj
    rw [h1S] at h
    exact h
  have hexpand : ((L * (1 - S))†) * (L * (1 - S)) =
      (1 - S) * ((L†) * L) * (1 - S) := by
    rw [hadj]
    noncomm_ring
  have hmid : (1 - S) * ((L†) * L) * (1 - S) =ₖ (1 - S) * S * (1 - S) :=
    CompactOperatorEq.right_mul (CompactOperatorEq.left_mul (1 - S) hLS) (1 - S)
  have hzero : (1 - S) * S * (1 - S) =ₖ 0 := by
    have hsplit : (1 - S) * S * (1 - S) = (S - S * S) + (S * S * S - S * S) := by
      noncomm_ring
    have hleft : IsCompactOperator ((S - S * S : H →L[ℂ] H)) := by
      have h := hSS
      rw [CompactOperatorEq] at h
      have hneg : (S - S * S : H →L[ℂ] H) = -(S * S - S) := by abel
      rw [hneg]
      exact h.neg
    have hright : IsCompactOperator ((S * S * S - S * S : H →L[ℂ] H)) := by
      have h := hSS
      rw [CompactOperatorEq] at h
      have heq : (S * S * S - S * S : H →L[ℂ] H) = (S * S - S) * S := by noncomm_ring
      rw [heq]
      exact h.comp_clm S
    rw [CompactOperatorEq, hsplit, sub_zero]
    exact hleft.add hright
  rw [hexpand]
  exact hmid.trans hzero

/-- The final Calkin projection congruence of a partial isometry follows from the initial
one: `(L L†)² ≡ L (L† L) L† ≡ L S L† ≡ L L†` modulo compact operators. -/
theorem mul_adjoint_sq_compactEq_of_adjoint_mul_compactEq
    (L S : H →L[ℂ] H) (hSadj : (S†) = S)
    (hLS : (L†) * L =ₖ S) (hSS : S * S =ₖ S) :
    (L * (L†)) * (L * (L†)) =ₖ L * (L†) := by
  have hone : IsCompactOperator ((L * (1 - S) : H →L[ℂ] H)) :=
    isCompactOperator_mul_one_sub_of_compactEq L S hSadj hLS hSS
  have h1 : (L * (L†)) * (L * (L†)) = L * ((L†) * L) * (L†) := by noncomm_ring
  have h2 : L * ((L†) * L) * (L†) =ₖ L * S * (L†) :=
    CompactOperatorEq.right_mul (CompactOperatorEq.left_mul L hLS) (L†)
  have h3 : L * S * (L†) =ₖ L * (L†) := by
    rw [CompactOperatorEq]
    have heq : L * S * (L†) - L * (L†) = -((L * (1 - S)) * (L†)) := by noncomm_ring
    rw [heq]
    exact (hone.comp_clm (L†)).neg
  exact (CompactOperatorEq.of_eq h1).trans (h2.trans h3)

end UpperBound

end RHTower
