import GaloisForLFunctions.HTGeometry.HolomorphicRieszFamily

/-!
# Analytic continuation of `exp(−Σ zₙ/n)` from approximate traces

Let `X` be a bounded operator with the circle `|w| = ρ` in its resolvent set, `P` its Riesz
projection, `Q = 1 − P` and `W = ran Q` finite dimensional.  For a sequence `z` set

  `localValue X ρ z = det(1 − X|_W) · exp(−Σ_{n≥1} (zₙ − tr(Xⁿ|_W))/n)`.

* `localValue_eq_of_lt` — **independence of the radius**: for `ρ < ρ' < 1` the two values agree.
  The space between the circles, `ran(P_{ρ'} − P_ρ)`, carries the eigenvalues of modulus in
  `(ρ, ρ')`; its determinant is `exp(−Σ trⁿ/n)` because those traces decay like `ρ'ⁿ`.
* `localValue_eq_exp_of_norm_pow_le` — if `‖Xⁿ‖ ≤ c τⁿ` with `τ < 1`, the local value is
  `exp(−Σ zₙ/n)`.
* `exists_continuation` — if `s ↦ T(s)` is holomorphic, every point has an admissible circle, and
  near each point and admissible circle the defects `zₙ(s) − tr(T(s)ⁿ|_W)` are uniformly summable
  after division by `n`, the local values glue to a holomorphic function equal to
  `exp(−Σ zₙ(s)/n)` wherever `‖T(s)ⁿ‖` decays geometrically.
-/

namespace GaloisForLFunctions.HTGeometry

open Metric Filter Topology FiniteRank Module

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The outer spectral projection `Q = 1 − P_ρ`. -/
def outerProj (X : E →L[ℂ] E) (ρ : ℝ) : E →L[ℂ] E := 1 - rieszProjection X 0 ρ

/-- The outer traces `tr(Xⁿ Q)`. -/
def outerTrace (X : E →L[ℂ] E) (ρ : ℝ) (n : ℕ) : ℂ := finiteRankTrace (X ^ n * outerProj X ρ)

/-- The outer determinant `det(1 − X Q)`. -/
def outerDet (X : E →L[ℂ] E) (ρ : ℝ) : ℂ := finiteRankDet (X * outerProj X ρ)

/-- The **local value** `det(1 − X|_W) exp(−Σ_{n≥1} (zₙ − tr(Xⁿ|_W))/n)`. -/
def localValue (X : E →L[ℂ] E) (ρ : ℝ) (z : ℕ → ℂ) : ℂ :=
  outerDet X ρ * Complex.exp (-∑' n : ℕ, (z (n + 1) - outerTrace X ρ (n + 1)) / ((n : ℂ) + 1))

/-! ## The outer subspace -/

section Structure

variable {X : E →L[ℂ] E} {ρ : ℝ}

theorem outerProj_mul_self (hρ : 0 < ρ) (h : ∀ w ∈ sphere (0 : ℂ) ρ, w ∈ resolventSet ℂ X) :
    outerProj X ρ * outerProj X ρ = outerProj X ρ := by
  have hPP := rieszProjection_mul_self_of_sphere X hρ h
  simp only [outerProj, sub_mul, mul_sub, one_mul, mul_one, hPP, sub_self, sub_zero]

theorem commute_outerProj (hρ : 0 < ρ) (h : ∀ w ∈ sphere (0 : ℂ) ρ, w ∈ resolventSet ℂ X) :
    X * outerProj X ρ = outerProj X ρ * X := by
  have hc := rieszProjection_commute X hρ.le h
  simp only [outerProj, mul_sub, sub_mul, mul_one, one_mul, hc]

theorem outerProj_apply_of_mem (hρ : 0 < ρ) (h : ∀ w ∈ sphere (0 : ℂ) ρ, w ∈ resolventSet ℂ X)
    {w : E} (hw : w ∈ opRange (outerProj X ρ)) : outerProj X ρ w = w := by
  obtain ⟨v, rfl⟩ := hw
  show (outerProj X ρ * outerProj X ρ) v = outerProj X ρ v
  rw [outerProj_mul_self hρ h]

theorem mapsTo_opRange_outerProj (hρ : 0 < ρ)
    (h : ∀ w ∈ sphere (0 : ℂ) ρ, w ∈ resolventSet ℂ X) :
    ∀ w ∈ opRange (outerProj X ρ), X w ∈ opRange (outerProj X ρ) := by
  rintro _ ⟨v, rfl⟩
  refine ⟨X v, ?_⟩
  show (outerProj X ρ * X) v = (X * outerProj X ρ) v
  rw [commute_outerProj hρ h]

omit [CompleteSpace E] in
theorem coe_restrictEnd_pow_apply (Y : E →L[ℂ] E) (W : Submodule ℂ E)
    (hY : ∀ w ∈ W, Y w ∈ W) (n : ℕ) (w : W) :
    (((restrictEnd Y W hY) ^ n) w : E) = (Y ^ n) w := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, coe_restrictEnd_apply, ih, pow_succ']
    rfl

theorem outerTrace_eq_trace (hρ : 0 < ρ) (h : ∀ w ∈ sphere (0 : ℂ) ρ, w ∈ resolventSet ℂ X)
    [FiniteDimensional ℂ (opRange (outerProj X ρ))] (n : ℕ) :
    outerTrace X ρ n = LinearMap.trace ℂ (opRange (outerProj X ρ))
      ((restrictEnd X (opRange (outerProj X ρ)) (mapsTo_opRange_outerProj hρ h)) ^ n) := by
  have hmem : ∀ v, (X ^ n * outerProj X ρ) v ∈ opRange (outerProj X ρ) := by
    intro v
    have hc : X ^ n * outerProj X ρ = outerProj X ρ * X ^ n :=
      ((Commute.pow_left (commute_outerProj hρ h) n)).eq
    rw [hc]
    exact mem_opRange _ _
  rw [outerTrace, finiteRankTrace_eq_trace_restrict _ _ hmem]
  congr 1
  ext w
  rw [coe_restrictEnd_apply, coe_restrictEnd_pow_apply]
  show (X ^ n) (outerProj X ρ w) = _
  rw [outerProj_apply_of_mem hρ h w.2]

theorem outerDet_eq_det (hρ : 0 < ρ) (h : ∀ w ∈ sphere (0 : ℂ) ρ, w ∈ resolventSet ℂ X)
    [FiniteDimensional ℂ (opRange (outerProj X ρ))] :
    outerDet X ρ = LinearMap.det
      (1 - restrictEnd X (opRange (outerProj X ρ)) (mapsTo_opRange_outerProj hρ h)) := by
  have hmem : ∀ v, (X * outerProj X ρ) v ∈ opRange (outerProj X ρ) := by
    intro v
    rw [commute_outerProj hρ h]
    exact mem_opRange _ _
  rw [outerDet, finiteRankDet_eq_det_restrict _ _ hmem]
  congr 2
  ext w
  rw [coe_restrictEnd_apply, coe_restrictEnd_apply]
  show X (outerProj X ρ w) = _
  rw [outerProj_apply_of_mem hρ h w.2]

end Structure

/-! ## Independence of the radius -/

/-- The trace series at `λ = 1`, written with `n + 1` in the denominator. -/
theorem traceSeries_one_eq (T : ℕ → ℂ) :
    GeomFredholm.traceSeries T 1 = ∑' n : ℕ, T (n + 1) / ((n : ℂ) + 1) := by
  unfold GeomFredholm.traceSeries
  refine tsum_congr fun n => ?_
  push_cast
  rw [one_pow, one_div, inv_mul_eq_div]

theorem summable_div_of_norm_le_geometric {T : ℕ → ℂ} {K c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hT : ∀ n, ‖T (n + 1)‖ ≤ K * c ^ (n + 1)) :
    Summable fun n : ℕ => T (n + 1) / ((n : ℂ) + 1) := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hc0 hc1).mul_left (K * c))
    fun n => ?_
  have h1 : (1 : ℝ) ≤ ‖(n : ℂ) + 1‖ := by
    rw [show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
    exact_mod_cast Nat.succ_pos n
  rw [norm_div]
  calc ‖T (n + 1)‖ / ‖(n : ℂ) + 1‖ ≤ ‖T (n + 1)‖ := div_le_self (norm_nonneg _) h1
    _ ≤ K * c ^ (n + 1) := hT n
    _ = K * c * c ^ n := by ring

/-- **The local value does not depend on the radius.** -/
theorem localValue_eq_of_lt {X : E →L[ℂ] E} {ρ ρ' : ℝ} (hρ : 0 < ρ) (hρρ' : ρ < ρ')
    (hρ'1 : ρ' < 1) (h : ∀ w ∈ sphere (0 : ℂ) ρ, w ∈ resolventSet ℂ X)
    (h' : ∀ w ∈ sphere (0 : ℂ) ρ', w ∈ resolventSet ℂ X)
    [FiniteDimensional ℂ (opRange (outerProj X ρ))] {z : ℕ → ℂ}
    (hs : Summable fun n : ℕ => (z (n + 1) - outerTrace X ρ (n + 1)) / ((n : ℂ) + 1)) :
    localValue X ρ z = localValue X ρ' z := by
  have hρ' : 0 < ρ' := hρ.trans hρρ'
  set P := rieszProjection X 0 ρ with hPdef
  set P' := rieszProjection X 0 ρ' with hP'def
  have hPP' : P * P' = P := rieszProjection_mul_of_lt X hρ hρρ' h h'
  have hP'P : P' * P = P := rieszProjection_mul_of_lt' X hρ hρρ' h h'
  have hPP : P * P = P := rieszProjection_mul_self_of_sphere X hρ h
  have hP'P' : P' * P' = P' := rieszProjection_mul_self_of_sphere X hρ' h'
  have hXP : X * P = P * X := rieszProjection_commute X hρ.le h
  have hXP' : X * P' = P' * X := rieszProjection_commute X hρ'.le h'
  set B : E →L[ℂ] E := P' - P with hBdef
  have hQeq : outerProj X ρ = outerProj X ρ' + B := by
    simp only [outerProj, B, ← hPdef, ← hP'def]; abel
  have hQQ' : outerProj X ρ * outerProj X ρ' = outerProj X ρ' := by
    simp only [outerProj, ← hPdef, ← hP'def, sub_mul, mul_sub, one_mul, mul_one, hPP']; abel
  have hQB : outerProj X ρ * B = B := by
    simp only [outerProj, B, ← hPdef, sub_mul, mul_sub, one_mul, hPP', hPP]; abel
  have hBB : B * B = B := by
    simp only [B, sub_mul, mul_sub, hP'P', hP'P, hPP', hPP]; abel
  have hXB : X * B = B * X := by simp only [B, mul_sub, sub_mul, hXP, hXP']
  set W := opRange (outerProj X ρ)
  set Wb := opRange B
  have hWbW : Wb ≤ W := by
    rintro _ ⟨v, rfl⟩
    refine ⟨B v, ?_⟩
    show (outerProj X ρ * B) v = B v
    rw [hQB]
  haveI : FiniteDimensional ℂ Wb := Submodule.finiteDimensional_of_le hWbW
  have hW'W : opRange (outerProj X ρ') ≤ W := by
    rintro _ ⟨v, rfl⟩
    refine ⟨outerProj X ρ' v, ?_⟩
    show (outerProj X ρ * outerProj X ρ') v = _
    rw [hQQ']
    rfl
  haveI : FiniteDimensional ℂ (opRange (outerProj X ρ')) := Submodule.finiteDimensional_of_le hW'W
  have hBfix : ∀ w ∈ Wb, B w = w := by
    rintro _ ⟨v, rfl⟩
    show (B * B) v = B v
    rw [hBB]
  have hXWb : ∀ w ∈ Wb, X w ∈ Wb := by
    rintro _ ⟨v, rfl⟩
    refine ⟨X v, ?_⟩
    show (B * X) v = (X * B) v
    rw [hXB]
  have hXnB : ∀ n, X ^ n * B = B * X ^ n := fun n => (Commute.pow_left hXB n).eq
  -- traces add
  have htrb : ∀ n, finiteRankTrace (X ^ n * B) =
      LinearMap.trace ℂ Wb ((restrictEnd X Wb hXWb) ^ n) := by
    intro n
    have hmb : ∀ v, (X ^ n * B) v ∈ Wb := fun v => by rw [hXnB]; exact mem_opRange _ _
    rw [finiteRankTrace_eq_trace_restrict _ Wb hmb]
    congr 1
    ext w
    rw [coe_restrictEnd_apply, coe_restrictEnd_pow_apply]
    show (X ^ n) (B w) = _
    rw [hBfix _ w.2]
  have htr : ∀ n, outerTrace X ρ n = outerTrace X ρ' n +
      LinearMap.trace ℂ Wb ((restrictEnd X Wb hXWb) ^ n) := by
    intro n
    have hc' : X ^ n * outerProj X ρ' = outerProj X ρ' * X ^ n :=
      (Commute.pow_left (commute_outerProj hρ' h') n).eq
    have hm1 : ∀ v, (X ^ n * outerProj X ρ') v ∈ W := fun v =>
      hW'W (by rw [hc']; exact mem_opRange _ _)
    have hm2 : ∀ v, (X ^ n * B) v ∈ W := fun v => hWbW (by rw [hXnB]; exact mem_opRange _ _)
    rw [outerTrace, hQeq, mul_add, finiteRankTrace_add_of_le _ _ W hm1 hm2, ← htrb]
    rfl
  -- determinants multiply
  have hdet : outerDet X ρ = outerDet X ρ' * LinearMap.det (1 - restrictEnd X Wb hXWb) := by
    rw [outerDet_eq_det hρ h, outerDet_eq_det hρ' h']
    refine det_one_sub_eq_mul_of_trace_pow_eq_add _ _ _ fun n => ?_
    rw [← outerTrace_eq_trace hρ h, ← outerTrace_eq_trace hρ' h', htr]
  -- the middle block has geometrically decaying traces
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_norm_resolvent_le_on_sphere X h
  obtain ⟨Λ', hΛ'0, hΛ'⟩ := exists_norm_resolvent_le_on_sphere X h'
  set K : ℝ := finrank ℂ Wb * ((Λ' + Λ) * ρ')
  have hbtw : ∀ n : ℕ, ‖LinearMap.trace ℂ Wb ((restrictEnd X Wb hXWb) ^ (n + 1))‖ ≤
      K * ρ' ^ (n + 1) := by
    intro n
    rw [← htrb]
    have hmb : ∀ v, (X ^ (n + 1) * B) v ∈ Wb := fun v => by rw [hXnB]; exact mem_opRange _ _
    refine (norm_finiteRankTrace_le _ Wb hmb).trans ?_
    have hB : ‖X ^ (n + 1) * B‖ ≤ (Λ' + Λ) * ρ' * ρ' ^ (n + 1) := by
      have e1 := norm_pow_mul_rieszProjection_le X hρ'.le h' hΛ' (n + 1)
      have e2 := norm_pow_mul_rieszProjection_le X hρ.le h hΛ (n + 1)
      have e3 : ρ ^ (n + 1 + 1) ≤ ρ' ^ (n + 1 + 1) := pow_le_pow_left₀ hρ.le hρρ'.le _
      calc ‖X ^ (n + 1) * B‖ = ‖X ^ (n + 1) * P' - X ^ (n + 1) * P‖ := by rw [hBdef, mul_sub]
        _ ≤ ‖X ^ (n + 1) * P'‖ + ‖X ^ (n + 1) * P‖ := norm_sub_le _ _
        _ ≤ ρ' ^ (n + 1 + 1) * Λ' + ρ ^ (n + 1 + 1) * Λ := add_le_add e1 e2
        _ ≤ ρ' ^ (n + 1 + 1) * Λ' + ρ' ^ (n + 1 + 1) * Λ := by gcongr
        _ = (Λ' + Λ) * ρ' * ρ' ^ (n + 1) := by ring
    calc (finrank ℂ Wb : ℝ) * ‖X ^ (n + 1) * B‖
        ≤ finrank ℂ Wb * ((Λ' + Λ) * ρ' * ρ' ^ (n + 1)) :=
          mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg _)
      _ = K * ρ' ^ (n + 1) := by simp only [K]; ring
  have hdetb := det_one_sub_eq_exp_of_norm_trace_pow_le (restrictEnd X Wb hXWb) hρ'.le hρ'1 hbtw
  rw [traceSeries_one_eq] at hdetb
  have hsb := summable_div_of_norm_le_geometric
    (T := fun n => LinearMap.trace ℂ Wb ((restrictEnd X Wb hXWb) ^ n)) hρ'.le hρ'1 hbtw
  rw [localValue, localValue, hdet, hdetb, mul_assoc, ← Complex.exp_add]
  congr 2
  rw [← neg_add, ← hsb.tsum_add hs]
  congr 1
  refine tsum_congr fun n => ?_
  rw [htr]
  ring

/-- **The local value is `exp(−Σ zₙ/n)` when the powers decay geometrically.** -/
theorem localValue_eq_exp_of_norm_pow_le {X : E →L[ℂ] E} {ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ w ∈ sphere (0 : ℂ) ρ, w ∈ resolventSet ℂ X)
    [FiniteDimensional ℂ (opRange (outerProj X ρ))] {c τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hX : ∀ n, ‖X ^ n‖ ≤ c * τ ^ n) {z : ℕ → ℂ}
    (hz : Summable fun n : ℕ => z (n + 1) / ((n : ℂ) + 1)) :
    localValue X ρ z = Complex.exp (-∑' n : ℕ, z (n + 1) / ((n : ℂ) + 1)) := by
  set W := opRange (outerProj X ρ)
  set K : ℝ := finrank ℂ W * (c * ‖outerProj X ρ‖)
  have hbound : ∀ n : ℕ, ‖LinearMap.trace ℂ W
      ((restrictEnd X W (mapsTo_opRange_outerProj hρ h)) ^ (n + 1))‖ ≤ K * τ ^ (n + 1) := by
    intro n
    rw [← outerTrace_eq_trace hρ h, outerTrace]
    have hm : ∀ v, (X ^ (n + 1) * outerProj X ρ) v ∈ W := fun v => by
      rw [(Commute.pow_left (commute_outerProj hρ h) (n + 1)).eq]; exact mem_opRange _ _
    refine (norm_finiteRankTrace_le _ W hm).trans ?_
    calc (finrank ℂ W : ℝ) * ‖X ^ (n + 1) * outerProj X ρ‖
        ≤ finrank ℂ W * (c * τ ^ (n + 1) * ‖outerProj X ρ‖) := by
          refine mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans ?_) (Nat.cast_nonneg _)
          exact mul_le_mul_of_nonneg_right (hX _) (norm_nonneg _)
      _ = K * τ ^ (n + 1) := by simp only [K]; ring
  have hdet := det_one_sub_eq_exp_of_norm_trace_pow_le _ hτ0 hτ1 hbound
  rw [traceSeries_one_eq] at hdet
  have hst := summable_div_of_norm_le_geometric
    (T := fun n => LinearMap.trace ℂ W ((restrictEnd X W (mapsTo_opRange_outerProj hρ h)) ^ n))
    hτ0 hτ1 hbound
  have htr : ∀ n, outerTrace X ρ n = LinearMap.trace ℂ W
      ((restrictEnd X W (mapsTo_opRange_outerProj hρ h)) ^ n) := outerTrace_eq_trace hρ h
  rw [localValue, outerDet_eq_det hρ h, hdet, ← Complex.exp_add]
  congr 1
  simp only [← htr] at hst ⊢
  have hs2 : Summable fun n : ℕ => (z (n + 1) - outerTrace X ρ (n + 1)) / ((n : ℂ) + 1) :=
    (hz.sub hst).congr fun n => by ring
  rw [← neg_add, ← hst.tsum_add hs2]
  congr 1
  refine tsum_congr fun n => ?_
  ring

/-! ## Gluing the local values -/

/-- A radius in `[ρ₁, ρ₂]` whose circle lies in the resolvent set. -/
def IsAdmissibleRadius (X : E →L[ℂ] E) (ρ₁ ρ₂ ρ : ℝ) : Prop :=
  ρ ∈ Set.Icc ρ₁ ρ₂ ∧ ∀ w ∈ sphere (0 : ℂ) ρ, w ∈ resolventSet ℂ X

/-- Holomorphy of the outer spectral data on an open set where a fixed circle is admissible. -/
theorem differentiableOn_outer {T : ℂ → E →L[ℂ] E} {B : Set ℂ} (hB : IsOpen B)
    (hT : DifferentiableOn ℂ T B) {ρ : ℝ} (hρ : 0 < ρ)
    (hres : ∀ s ∈ B, ∀ w ∈ sphere (0 : ℂ) ρ, w ∈ resolventSet ℂ (T s))
    (hfin : ∀ s ∈ B, FiniteDimensional ℂ (opRange (outerProj (T s) ρ))) :
    DifferentiableOn ℂ (fun s => outerDet (T s) ρ) B ∧
      ∀ n, DifferentiableOn ℂ (fun s => outerTrace (T s) ρ n) B := by
  have hP : DifferentiableOn ℂ (fun s => rieszProjection (T s) 0 ρ) B :=
    differentiableOn_rieszProjection_family hB hT hρ hres
  have key : ∀ (Y : ℂ → E →L[ℂ] E), DifferentiableOn ℂ Y B →
      (∀ s ∈ B, Y s * rieszProjection (T s) 0 ρ = rieszProjection (T s) 0 ρ * Y s) →
      DifferentiableOn ℂ (fun s => finiteRankTrace (Y s * outerProj (T s) ρ)) B ∧
      DifferentiableOn ℂ (fun s => finiteRankDet (Y s * outerProj (T s) ρ)) B := by
    intro Y hY hYP
    have hall : ∀ s₁ ∈ B,
        DifferentiableAt ℂ (fun s => finiteRankTrace (Y s * outerProj (T s) ρ)) s₁ ∧
        DifferentiableAt ℂ (fun s => finiteRankDet (Y s * outerProj (T s) ρ)) s₁ := by
      intro s₁ hs₁
      haveI : FiniteDimensional ℂ (opRange (1 - rieszProjection (T s₁) 0 ρ)) := hfin s₁ hs₁
      have hnhds : B ∈ 𝓝 s₁ := hB.mem_nhds hs₁
      exact differentiableAt_finiteRank_outer (P := fun s => rieszProjection (T s) 0 ρ)
        (Filter.eventually_of_mem hnhds fun s hs => (hP s hs).differentiableAt (hB.mem_nhds hs))
        (Filter.eventually_of_mem hnhds fun s hs =>
          rieszProjection_mul_self_of_sphere (T s) hρ (hres s hs))
        ((hY s₁ hs₁).differentiableAt hnhds)
        (Filter.eventually_of_mem hnhds hYP)
    exact ⟨fun s hs => (hall s hs).1.differentiableWithinAt,
      fun s hs => (hall s hs).2.differentiableWithinAt⟩
  have hcomm : ∀ s ∈ B, T s * rieszProjection (T s) 0 ρ = rieszProjection (T s) 0 ρ * T s :=
    fun s hs => rieszProjection_commute (T s) hρ.le (hres s hs)
  refine ⟨(key T hT hcomm).2, fun n => (key (fun s => T s ^ n) ?_ ?_).1⟩
  · exact fun s hs => (hT s hs).pow n
  · intro s hs
    exact (Commute.pow_left (hcomm s hs) n).eq

/-- **The continuation theorem.**  The local values glue to a function holomorphic on `Ω`, equal to
`exp(−Σ zₙ(s)/n)` wherever the powers of `T(s)` decay geometrically. -/
theorem exists_continuation {T : ℂ → E →L[ℂ] E} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hT : DifferentiableOn ℂ T Ω) {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (hρ₂ : ρ₂ < 1)
    {z : ℕ → ℂ → ℂ} (hz : ∀ n, Differentiable ℂ (z n))
    (hexists : ∀ s ∈ Ω, ∃ ρ, IsAdmissibleRadius (T s) ρ₁ ρ₂ ρ)
    (hfin : ∀ s ∈ Ω, ∀ ρ, IsAdmissibleRadius (T s) ρ₁ ρ₂ ρ →
      FiniteDimensional ℂ (opRange (outerProj (T s) ρ)))
    (hloc : ∀ s₀ ∈ Ω, ∀ ρ, IsAdmissibleRadius (T s₀) ρ₁ ρ₂ ρ → ∃ V ∈ 𝓝 s₀, ∃ u : ℕ → ℝ,
      Summable u ∧ ∀ s ∈ V, IsAdmissibleRadius (T s) ρ₁ ρ₂ ρ ∧
        ∀ n, ‖(z (n + 1) s - outerTrace (T s) ρ (n + 1)) / ((n : ℂ) + 1)‖ ≤ u n) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F Ω ∧
      ∀ s ∈ Ω, ∀ c τ : ℝ, 0 ≤ τ → τ < 1 → (∀ n, ‖T s ^ n‖ ≤ c * τ ^ n) →
        Summable (fun n : ℕ => z (n + 1) s / ((n : ℂ) + 1)) →
        F s = Complex.exp (-∑' n : ℕ, z (n + 1) s / ((n : ℂ) + 1)) := by
  have hex' : ∀ s, ∃ ρ, s ∈ Ω → IsAdmissibleRadius (T s) ρ₁ ρ₂ ρ := by
    intro s
    by_cases hs : s ∈ Ω
    · obtain ⟨ρ, hρ⟩ := hexists s hs
      exact ⟨ρ, fun _ => hρ⟩
    · exact ⟨0, fun h => absurd h hs⟩
  choose radius hradius using hex'
  have hsum : ∀ s ∈ Ω, ∀ ρ, IsAdmissibleRadius (T s) ρ₁ ρ₂ ρ →
      Summable fun n : ℕ => (z (n + 1) s - outerTrace (T s) ρ (n + 1)) / ((n : ℂ) + 1) := by
    intro s hs ρ hρ
    obtain ⟨V, hV, u, hu, hb⟩ := hloc s hs ρ hρ
    exact Summable.of_norm_bounded hu (hb s (mem_of_mem_nhds hV)).2
  -- any two admissible radii give the same local value
  have hagree : ∀ s ∈ Ω, ∀ ρ ρ', IsAdmissibleRadius (T s) ρ₁ ρ₂ ρ →
      IsAdmissibleRadius (T s) ρ₁ ρ₂ ρ' →
      localValue (T s) ρ (fun n => z n s) = localValue (T s) ρ' (fun n => z n s) := by
    intro s hs ρ ρ' hρ hρ'
    rcases lt_trichotomy ρ ρ' with hlt | heq | hgt
    · haveI := hfin s hs ρ hρ
      exact localValue_eq_of_lt (z := fun n => z n s) (hρ₁.trans_le hρ.1.1) hlt
        (hρ'.1.2.trans_lt hρ₂) hρ.2 hρ'.2 (hsum s hs ρ hρ)
    · rw [heq]
    · haveI := hfin s hs ρ' hρ'
      exact (localValue_eq_of_lt (z := fun n => z n s) (hρ₁.trans_le hρ'.1.1) hgt
        (hρ.1.2.trans_lt hρ₂) hρ'.2 hρ.2 (hsum s hs ρ' hρ')).symm
  refine ⟨fun s => localValue (T s) (radius s) (fun n => z n s), fun s₀ hs₀ => ?_,
    fun s hs c τ hτ0 hτ1 hdecay hzs => ?_⟩
  · obtain ⟨ρ₀, hρ₀def⟩ : ∃ ρ₀, ρ₀ = radius s₀ := ⟨_, rfl⟩
    have hadm₀ : IsAdmissibleRadius (T s₀) ρ₁ ρ₂ ρ₀ := hρ₀def ▸ hradius s₀ hs₀
    obtain ⟨V, hV, u, hu, hb⟩ := hloc s₀ hs₀ ρ₀ hadm₀
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hV (hΩ.mem_nhds hs₀))
    set B := ball s₀ δ
    have hBV : ∀ s ∈ B, s ∈ V := fun s h => (hball h).1
    have hBΩ : ∀ s ∈ B, s ∈ Ω := fun s h => (hball h).2
    have hρ₀ : 0 < ρ₀ := hρ₁.trans_le hadm₀.1.1
    have hres : ∀ s ∈ B, ∀ w ∈ sphere (0 : ℂ) ρ₀, w ∈ resolventSet ℂ (T s) :=
      fun s hs => (hb s (hBV s hs)).1.2
    obtain ⟨hdetD, htrD⟩ := differentiableOn_outer isOpen_ball (hT.mono fun s h => hBΩ s h) hρ₀ hres
      (fun s hs => hfin s (hBΩ s hs) ρ₀ (hb s (hBV s hs)).1)
    have hseries : DifferentiableOn ℂ (fun s => ∑' n : ℕ,
        (z (n + 1) s - outerTrace (T s) ρ₀ (n + 1)) / ((n : ℂ) + 1)) B := by
      refine Complex.differentiableOn_tsum_of_summable_norm hu (fun n => ?_) isOpen_ball
        (fun n s hs => (hb s (hBV s hs)).2 n)
      exact (((hz (n + 1)).differentiableOn).sub (htrD (n + 1))).div_const _
    have hG : DifferentiableOn ℂ (fun s => localValue (T s) ρ₀ (fun n => z n s)) B :=
      hdetD.mul hseries.neg.cexp
    have heq : (fun s => localValue (T s) (radius s) (fun n => z n s)) =ᶠ[𝓝 s₀]
        fun s => localValue (T s) ρ₀ (fun n => z n s) := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hδ)] with s hs
      exact hagree s (hBΩ s hs) _ _ (hradius s (hBΩ s hs)) (hb s (hBV s hs)).1
    exact ((hG s₀ (mem_ball_self hδ)).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self hδ))).congr_of_eventuallyEq heq |>.differentiableWithinAt
  · haveI := hfin s hs _ (hradius s hs)
    exact localValue_eq_exp_of_norm_pow_le (z := fun n => z n s)
      (hρ₁.trans_le (hradius s hs).1.1) (hradius s hs).2 hτ0 hτ1 hdecay hzs

end

end GaloisForLFunctions.HTGeometry
