import GaloisForLFunctions.RHTower.BaezDuarteDetectorGram
import GaloisForLFunctions.RHTower.BaezDuarteDistance


/-!
# The sharp Blaschke floor for the Báez-Duarte distances

For distinct zeros `ρ₁, …, ρ_n` of `ζ` with `½ < Re ρ_i < 1`, every element `G` of the closed span
of the Báez-Duarte generators satisfies

`‖target − G‖² ≥ 1 − Π |1 − ρ_i|²/|ρ_i|²`

(`one_sub_prod_le_norm_bdTarget_sub_sq`), hence `d_N² ≥ 1 − Π |1 − ρ_i|²/|ρ_i|²` for every `N`
(`one_sub_prod_le_bdDistDiscrete_sq`) and, in exponential form,
`d_N² ≥ 1 − exp(−2 Σ log(|ρ_i|/|1 − ρ_i|))` (`one_sub_exp_le_bdDistDiscrete_sq`): the exponent is the
Balazard–Saias–Yor sum of the zeros.

**Proof.**  The detector of a point `z` (`pointDetector`, the detector at `1 − z`) has Gram
`⟪T_a, T_b⟫ = 1/(a + b̄ − 1)`, and `T_1` is the target.  Gram–Schmidt against the detectors of the
zeros (`detectorResidual`) has residual Gram `B(a) B̄(b)/(a + b̄ − 1)` with `B` the half-plane
Blaschke product `Π (z − ρ_i)/(z + ρ̄_i − 1)` (`inner_detectorResidual`): each step is the one-point
Schur complement of the Cauchy kernel (`cauchyKernel_schur`).  The target minus its residual lies in
the detector span, which annihilates the generators, and has squared norm `1 − |B(1)|²`.
-/

open Complex MeasureTheory Set Filter Topology ComplexConjugate

namespace RHTower

noncomputable section

/-! ## Detectors indexed by points of the half-plane -/

/-- The detector of a point `z` with `Re z > ½`; at `z = 1` it is the target. -/
def pointDetector (z : ℂ) : BDCarrier :=
  if h : 1 / 2 < z.re then bdDetector (one_sub_re_lt h) else 0

theorem pointDetector_of_re {z : ℂ} (h : 1 / 2 < z.re) :
    pointDetector z = bdDetector (one_sub_re_lt h) := dif_pos h

theorem inner_pointDetector {a b : ℂ} (ha : 1 / 2 < a.re) (hb : 1 / 2 < b.re) :
    inner ℂ (pointDetector a) (pointDetector b) = 1 / (a + conj b - 1) := by
  rw [pointDetector_of_re ha, pointDetector_of_re hb, inner_bdDetector_bdDetector]
  congr 1
  simp only [map_sub, map_one]
  ring

theorem pointDetector_one : pointDetector 1 = bdTarget := by
  rw [pointDetector_of_re (by norm_num), bdDetector, bdTarget]
  refine MemLp.toLp_congr _ _ ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one hu
  simp only [bdDetectorFun, bdTargetFun, sub_self, zero_sub, Complex.cpow_neg_one, map_inv₀,
    Complex.conj_ofReal]

/-! ## Gram–Schmidt against detectors -/

/-- The Blaschke factor `(z − ρ)/(z + ρ̄ − 1)` of the half-plane `Re z > ½`. -/
def detectorBlaschkeFactor (ρ z : ℂ) : ℂ := (z - ρ) / (z + conj ρ - 1)

/-- The finite Blaschke product of a list of points. -/
def detectorBlaschke (l : List ℂ) (z : ℂ) : ℂ := (l.map fun ρ => detectorBlaschkeFactor ρ z).prod

/-- The residual of `pointDetector z` after projecting out the detectors of the points of `l`,
one at a time. -/
def detectorResidual : List ℂ → ℂ → BDCarrier
  | [], z => pointDetector z
  | ρ :: l, z => detectorResidual l z -
      (inner ℂ (detectorResidual l ρ) (detectorResidual l z) /
        inner ℂ (detectorResidual l ρ) (detectorResidual l ρ)) • detectorResidual l ρ

theorem detectorBlaschke_cons (ρ : ℂ) (l : List ℂ) (z : ℂ) :
    detectorBlaschke (ρ :: l) z = detectorBlaschkeFactor ρ z * detectorBlaschke l z := by
  simp [detectorBlaschke]

theorem add_conj_sub_one_ne_zero {a b : ℂ} (ha : 1 / 2 < a.re) (hb : 1 / 2 < b.re) :
    a + conj b - 1 ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

theorem detectorBlaschke_ne_zero {l : List ℂ} (hl : ∀ ρ ∈ l, 1 / 2 < ρ.re) {z : ℂ}
    (hz : 1 / 2 < z.re) (hzl : z ∉ l) : detectorBlaschke l z ≠ 0 := by
  induction l with
  | nil => simp [detectorBlaschke]
  | cons ρ l ih =>
    rw [detectorBlaschke_cons]
    refine mul_ne_zero (div_ne_zero (sub_ne_zero.mpr fun h => hzl (h ▸ List.mem_cons_self))
      (add_conj_sub_one_ne_zero hz (hl ρ List.mem_cons_self))) (ih (fun ρ' h => hl ρ'
        (List.mem_cons_of_mem _ h)) (fun h => hzl (List.mem_cons_of_mem _ h)))

/-- The one-point Schur complement of the Cauchy kernel `1/(a + b̄ − 1)`. -/
theorem cauchyKernel_schur {a b ρ : ℂ} (ha : 1 / 2 < a.re) (hb : 1 / 2 < b.re)
    (hρ : 1 / 2 < ρ.re) :
    1 / (a + conj b - 1) - (1 / (a + conj ρ - 1)) * (1 / (ρ + conj b - 1)) /
        (1 / (ρ + conj ρ - 1)) =
      detectorBlaschkeFactor ρ a * conj (detectorBlaschkeFactor ρ b) * (1 / (a + conj b - 1)) := by
  have h1 := add_conj_sub_one_ne_zero ha hb
  have h2 := add_conj_sub_one_ne_zero ha hρ
  have h3 := add_conj_sub_one_ne_zero hρ hb
  have h4 := add_conj_sub_one_ne_zero hρ hρ
  have h5 : conj b + ρ - 1 ≠ 0 := by
    intro h; apply h3; linear_combination h
  unfold detectorBlaschkeFactor
  rw [map_div₀, map_sub, map_sub, map_add, Complex.conj_conj, map_one]
  field_simp
  ring

/-- One Gram–Schmidt step: `⟪x − αf, y − βf⟫ = ⟪x, y⟫ − ⟪x, f⟫⟪f, y⟫/⟪f, f⟫`. -/
theorem inner_sub_proj_sub_proj {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (x y f : E) (hf : inner ℂ f f ≠ 0) :
    inner ℂ (x - (inner ℂ f x / inner ℂ f f) • f) (y - (inner ℂ f y / inner ℂ f f) • f) =
      inner ℂ x y - inner ℂ x f * inner ℂ f y / inner ℂ f f := by
  have hreal : conj (inner ℂ f f) = inner ℂ f f := inner_self_conj f
  have hxf : conj (inner ℂ f x) = inner ℂ x f := inner_conj_symm x f
  rw [inner_sub_left, inner_sub_right, inner_sub_right, inner_smul_left, inner_smul_right,
    inner_smul_right, inner_smul_left, map_div₀, hreal, hxf]
  field_simp
  ring

/-- **The residual Gram.**  `⟪r_l(a), r_l(b)⟫ = B_l(a) B̄_l(b)/(a + b̄ − 1)` for distinct points
of the half-plane. -/
theorem inner_detectorResidual (l : List ℂ) (hl : ∀ ρ ∈ l, 1 / 2 < ρ.re) (hnd : l.Nodup)
    {a b : ℂ} (ha : 1 / 2 < a.re) (hb : 1 / 2 < b.re) :
    inner ℂ (detectorResidual l a) (detectorResidual l b) =
      detectorBlaschke l a * conj (detectorBlaschke l b) * (1 / (a + conj b - 1)) := by
  induction l generalizing a b with
  | nil =>
    simp only [detectorResidual, detectorBlaschke, List.map_nil, List.prod_nil, map_one,
      one_mul]
    exact inner_pointDetector ha hb
  | cons ρ l ih =>
    have hρ : 1 / 2 < ρ.re := hl ρ List.mem_cons_self
    have hl' : ∀ ρ' ∈ l, 1 / 2 < ρ'.re := fun ρ' h => hl ρ' (List.mem_cons_of_mem _ h)
    have hρl : ρ ∉ l := (List.nodup_cons.mp hnd).1
    have hnd' : l.Nodup := (List.nodup_cons.mp hnd).2
    have IH := fun {a b : ℂ} (ha : 1 / 2 < a.re) (hb : 1 / 2 < b.re) => ih hl' hnd' ha hb
    have hBρ : detectorBlaschke l ρ ≠ 0 := detectorBlaschke_ne_zero hl' hρ hρl
    have hff : inner ℂ (detectorResidual l ρ) (detectorResidual l ρ) ≠ 0 := by
      rw [IH hρ hρ]
      exact mul_ne_zero (mul_ne_zero hBρ ((map_ne_zero _).mpr hBρ))
        (one_div_ne_zero (add_conj_sub_one_ne_zero hρ hρ))
    simp only [detectorResidual]
    rw [inner_sub_proj_sub_proj _ _ _ hff, IH ha hb, IH ha hρ, IH hρ hb, IH hρ hρ,
      detectorBlaschke_cons, detectorBlaschke_cons]
    set Ba := detectorBlaschke l a
    set Bb := detectorBlaschke l b
    set Bρ := detectorBlaschke l ρ
    have hconjB : conj Bρ ≠ 0 := (map_ne_zero _).mpr hBρ
    have hK := one_div_ne_zero (add_conj_sub_one_ne_zero hρ hρ)
    have hfac : Ba * conj Bb * (1 / (a + conj b - 1)) -
        Ba * conj Bρ * (1 / (a + conj ρ - 1)) * (Bρ * conj Bb * (1 / (ρ + conj b - 1))) /
          (Bρ * conj Bρ * (1 / (ρ + conj ρ - 1))) =
        Ba * conj Bb * (1 / (a + conj b - 1) - (1 / (a + conj ρ - 1)) * (1 / (ρ + conj b - 1)) /
          (1 / (ρ + conj ρ - 1))) := by
      field_simp
    rw [hfac, cauchyKernel_schur ha hb hρ, map_mul]
    ring

/-- The span of the detectors of the points of `l`. -/
def detectorSpan (l : List ℂ) : Submodule ℂ BDCarrier :=
  Submodule.span ℂ {x | ∃ ρ ∈ l, x = pointDetector ρ}

theorem detectorSpan_mono {ρ : ℂ} {l : List ℂ} : detectorSpan l ≤ detectorSpan (ρ :: l) :=
  Submodule.span_mono fun _ ⟨ρ', h, hx⟩ => ⟨ρ', List.mem_cons_of_mem _ h, hx⟩

theorem pointDetector_mem_detectorSpan {ρ : ℂ} {l : List ℂ} (h : ρ ∈ l) :
    pointDetector ρ ∈ detectorSpan l :=
  Submodule.subset_span ⟨ρ, h, rfl⟩

theorem detectorResidual_sub_mem (l : List ℂ) (z : ℂ) :
    detectorResidual l z - pointDetector z ∈ detectorSpan l := by
  induction l generalizing z with
  | nil => simp [detectorResidual]
  | cons ρ l ih =>
    simp only [detectorResidual]
    set α := inner ℂ (detectorResidual l ρ) (detectorResidual l z) /
      inner ℂ (detectorResidual l ρ) (detectorResidual l ρ)
    have h1 := detectorSpan_mono (ρ := ρ) (ih z)
    have h2 := detectorSpan_mono (ρ := ρ) (ih ρ)
    have h3 := pointDetector_mem_detectorSpan (List.mem_cons_self (a := ρ) (l := l))
    have e : detectorResidual l z - α • detectorResidual l ρ - pointDetector z =
        (detectorResidual l z - pointDetector z) -
          α • (detectorResidual l ρ - pointDetector ρ) - α • pointDetector ρ := by
      simp only [smul_sub]; abel
    rw [e]
    exact Submodule.sub_mem _ (Submodule.sub_mem _ h1 (Submodule.smul_mem _ _ h2))
      (Submodule.smul_mem _ _ h3)

theorem inner_detectorSpan_detectorResidual (l : List ℂ) (z : ℂ) {v : BDCarrier}
    (hv : v ∈ detectorSpan l) : inner ℂ v (detectorResidual l z) = 0 := by
  induction l generalizing z v with
  | nil =>
    simp only [detectorSpan, List.not_mem_nil, false_and, exists_false, Set.setOf_false,
      Submodule.span_empty, Submodule.mem_bot] at hv
    rw [hv, inner_zero_left]
  | cons ρ l ih =>
    simp only [detectorResidual]
    set f := detectorResidual l ρ
    set α := inner ℂ f (detectorResidual l z) / inner ℂ f f
    -- `f` itself is orthogonal to the residual
    have hf : inner ℂ f (detectorResidual l z - α • f) = 0 := by
      rw [inner_sub_right, inner_smul_right]
      by_cases hff : inner ℂ f f = 0
      · have : f = 0 := inner_self_eq_zero.mp hff
        rw [this]; simp
      · rw [div_mul_cancel₀ _ hff, sub_self]
    have hgen : ∀ x ∈ {x | ∃ ρ' ∈ ρ :: l, x = pointDetector ρ'},
        inner ℂ x (detectorResidual l z - α • f) = 0 := by
      rintro x ⟨ρ', hρ', rfl⟩
      rcases List.mem_cons.mp hρ' with h | h
      · subst h
        have hd := detectorResidual_sub_mem l ρ'
        have e : pointDetector ρ' = f - (f - pointDetector ρ') := by abel
        rw [e, inner_sub_left, hf, inner_sub_right, inner_smul_right, ih z hd, ih ρ' hd]
        simp
      · have hmem := pointDetector_mem_detectorSpan h
        rw [inner_sub_right, inner_smul_right, ih z hmem, ih ρ hmem]
        simp
    refine Submodule.span_induction (p := fun x _ => inner ℂ x (detectorResidual l z - α • f) = 0)
      hgen ?_ ?_ ?_ hv
    · simp
    · intro x y _ _ hx hy; rw [inner_add_left, hx, hy, add_zero]
    · intro c x _ hx; rw [inner_smul_left, hx, mul_zero]

/-! ## The sharp Blaschke floor -/

theorem norm_detectorBlaschke_one_sq (l : List ℂ) :
    ‖detectorBlaschke l 1‖ ^ 2 = (l.map fun ρ => ‖1 - ρ‖ ^ 2 / ‖ρ‖ ^ 2).prod := by
  induction l with
  | nil => simp [detectorBlaschke]
  | cons ρ l ih =>
    rw [detectorBlaschke_cons, norm_mul, mul_pow, ih, List.map_cons, List.prod_cons]
    congr 1
    unfold detectorBlaschkeFactor
    rw [norm_div, div_pow, show (1 : ℂ) + conj ρ - 1 = conj ρ by ring, Complex.norm_conj]

theorem inner_detectorSpan_closedSpan_eq_zero {l : List ℂ}
    (hl : ∀ ρ ∈ l, riemannZeta ρ = 0 ∧ 1 / 2 < ρ.re ∧ ρ.re < 1) {v G : BDCarrier}
    (hv : v ∈ detectorSpan l)
    (hG : G ∈ (Submodule.span ℂ (Set.range (fun i : bdIndex => bdGen i.1))).topologicalClosure) :
    inner ℂ v G = 0 := by
  have hgen : ∀ x ∈ {x | ∃ ρ ∈ l, x = pointDetector ρ}, inner ℂ x G = 0 := by
    rintro x ⟨ρ, hρ, rfl⟩
    obtain ⟨hz, h1, h2⟩ := hl ρ hρ
    rw [pointDetector_of_re h1]
    exact GaloisForLFunctions.HTGeometry.continuousLinearMap_eq_zero_on_closedSpan
      (innerSL ℂ (bdDetector (one_sub_re_lt h1))) (fun i : bdIndex => bdGen i.1)
      (fun i => inner_bdDetector_bdGen_eq_zero h1 h2 hz i) hG
  refine Submodule.span_induction (p := fun x _ => inner ℂ x G = 0) hgen ?_ ?_ ?_ hv
  · simp
  · intro x y _ _ hx hy; rw [inner_add_left, hx, hy, add_zero]
  · intro c x _ hx; rw [inner_smul_left, hx, mul_zero]

/-- **The sharp Blaschke floor.**  For distinct zeros `ρ₁, …, ρ_n` of `ζ` with `½ < Re ρ_i < 1`
and every `G` in the closed span of the Báez-Duarte generators,
`‖target − G‖² ≥ 1 − Π |1 − ρ_i|²/|ρ_i|²`.  The residual of the target after Gram–Schmidt
against the detectors of the zeros has squared norm `|B(1)|²`, `B` the half-plane Blaschke
product of the zeros. -/
theorem one_sub_prod_le_norm_bdTarget_sub_sq {l : List ℂ}
    (hl : ∀ ρ ∈ l, riemannZeta ρ = 0 ∧ 1 / 2 < ρ.re ∧ ρ.re < 1) (hnd : l.Nodup) {G : BDCarrier}
    (hG : G ∈ (Submodule.span ℂ (Set.range (fun i : bdIndex => bdGen i.1))).topologicalClosure) :
    1 - (l.map fun ρ => ‖1 - ρ‖ ^ 2 / ‖ρ‖ ^ 2).prod ≤ ‖bdTarget - G‖ ^ 2 := by
  have hl' : ∀ ρ ∈ l, 1 / 2 < ρ.re := fun ρ h => (hl ρ h).2.1
  have h1 : (1 / 2 : ℝ) < (1 : ℂ).re := by norm_num
  set r := detectorResidual l 1 with hr
  set w := bdTarget - r with hw
  have hwmem : w ∈ detectorSpan l := by
    have h := detectorResidual_sub_mem l 1
    rw [pointDetector_one] at h
    have : w = -(r - bdTarget) := by rw [hw]; abel
    rw [this]; exact Submodule.neg_mem _ h
  have hwG : inner ℂ w G = 0 := inner_detectorSpan_closedSpan_eq_zero hl hwmem hG
  have hwr : inner ℂ w r = 0 := inner_detectorSpan_detectorResidual l 1 hwmem
  -- the residual norm
  have hrr : ‖r‖ ^ 2 = (l.map fun ρ => ‖1 - ρ‖ ^ 2 / ‖ρ‖ ^ 2).prod := by
    have h := inner_detectorResidual l hl' hnd h1 h1
    rw [← hr, inner_self_eq_norm_sq_to_K, show (1 : ℂ) + conj 1 - 1 = 1 by simp, div_one,
      mul_one, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
    rw [← norm_detectorBlaschke_one_sq]
    have h2 : ((‖r‖ ^ 2 : ℝ) : ℂ) = ((‖detectorBlaschke l 1‖ ^ 2 : ℝ) : ℂ) := by
      rw [← h]; push_cast; rfl
    exact Complex.ofReal_injective h2
  -- Pythagoras
  have hpyth : ‖bdTarget‖ ^ 2 = ‖w‖ ^ 2 + ‖r‖ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) w r hwr
    rw [show w + r = bdTarget by rw [hw]; abel] at h
    nlinarith [h]
  rw [norm_bdTarget, one_pow, hrr] at hpyth
  have hwsq : ‖w‖ ^ 2 = 1 - (l.map fun ρ => ‖1 - ρ‖ ^ 2 / ‖ρ‖ ^ 2).prod := by linarith
  rw [← hwsq]
  -- Cauchy–Schwarz against `bdTarget − G`
  have hpair : inner ℂ w (bdTarget - G) = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_sub_right, hwG, sub_zero, show bdTarget = w + r by rw [hw]; abel, inner_add_right,
      hwr, add_zero, inner_self_eq_norm_sq_to_K]
    push_cast; rfl
  have hcs := norm_inner_le_norm (𝕜 := ℂ) w (bdTarget - G)
  rw [hpair, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)] at hcs
  rcases eq_or_lt_of_le (norm_nonneg w) with h0 | hpos
  · rw [← h0]; simp
  · have : ‖w‖ ≤ ‖bdTarget - G‖ := by nlinarith
    exact pow_le_pow_left₀ (norm_nonneg _) this 2

/-- The sharp floor for the Báez-Duarte distance of any family of dilations in `(0, 1]`. -/
theorem one_sub_prod_le_bdDist_sq {I : Type*} (θ : I → ℝ) (hθ : ∀ i, 0 < θ i ∧ θ i ≤ 1)
    {l : List ℂ} (hl : ∀ ρ ∈ l, riemannZeta ρ = 0 ∧ 1 / 2 < ρ.re ∧ ρ.re < 1) (hnd : l.Nodup) :
    1 - (l.map fun ρ => ‖1 - ρ‖ ^ 2 / ‖ρ‖ ^ 2).prod ≤ bdDist θ ^ 2 := by
  set P := (l.map fun ρ => ‖1 - ρ‖ ^ 2 / ‖ρ‖ ^ 2).prod with hP
  have hsub : bdSpanSet θ ⊆
      ((Submodule.span ℂ (Set.range (fun i : bdIndex => bdGen i.1))).topologicalClosure :
        Set BDCarrier) := by
    refine fun G hG => Submodule.le_topologicalClosure _ ?_
    refine (Submodule.span_mono ?_) hG
    rintro x ⟨i, rfl⟩
    exact ⟨⟨θ i, hθ i⟩, rfl⟩
  rcases le_or_gt (1 - P) 0 with hle | hpos
  · exact hle.trans (sq_nonneg _)
  have hsqrt : Real.sqrt (1 - P) ≤ bdDist θ := by
    refine (Metric.le_infDist (bdSpanSet_nonempty θ)).mpr fun G hG => ?_
    rw [dist_eq_norm]
    have h := one_sub_prod_le_norm_bdTarget_sub_sq hl hnd (hsub hG)
    rw [← hP] at h
    calc Real.sqrt (1 - P) ≤ Real.sqrt (‖bdTarget - G‖ ^ 2) := Real.sqrt_le_sqrt h
      _ = ‖bdTarget - G‖ := Real.sqrt_sq (norm_nonneg _)
  have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt 2
  rwa [Real.sq_sqrt hpos.le] at this

/-- **The sharp floor for the discrete distances.**  For every `N` and distinct zeros
`ρ₁, …, ρ_n` with `½ < Re ρ_i < 1`, `d_N² ≥ 1 − Π |1 − ρ_i|²/|ρ_i|²`. -/
theorem one_sub_prod_le_bdDistDiscrete_sq (N : ℕ) {l : List ℂ}
    (hl : ∀ ρ ∈ l, riemannZeta ρ = 0 ∧ 1 / 2 < ρ.re ∧ ρ.re < 1) (hnd : l.Nodup) :
    1 - (l.map fun ρ => ‖1 - ρ‖ ^ 2 / ‖ρ‖ ^ 2).prod ≤ bdDistDiscrete N ^ 2 := by
  refine one_sub_prod_le_bdDist_sq _ (fun i => ⟨?_, ?_⟩) hl hnd
  · simp only [bdDiscrete]; positivity
  · simp only [bdDiscrete]
    rw [div_le_one (by positivity)]
    linarith [(i.1 : ℕ).cast_nonneg (α := ℝ)]

/-- The floor in exponential form: `d_N² ≥ 1 − exp(−2 Σ log(|ρ_i|/|1 − ρ_i|))`, the exponent being
the Balazard–Saias–Yor sum of the zeros. -/
theorem one_sub_exp_le_bdDistDiscrete_sq (N : ℕ) {l : List ℂ}
    (hl : ∀ ρ ∈ l, riemannZeta ρ = 0 ∧ 1 / 2 < ρ.re ∧ ρ.re < 1) (hnd : l.Nodup) :
    1 - Real.exp (-2 * (l.map fun ρ => Real.log (‖ρ‖ / ‖1 - ρ‖)).sum) ≤
      bdDistDiscrete N ^ 2 := by
  have hprod : (l.map fun ρ => ‖1 - ρ‖ ^ 2 / ‖ρ‖ ^ 2).prod =
      Real.exp (-2 * (l.map fun ρ => Real.log (‖ρ‖ / ‖1 - ρ‖)).sum) := by
    induction l with
    | nil => simp
    | cons ρ l ih =>
      have hρ := hl ρ List.mem_cons_self
      have hρ0 : ρ ≠ 0 := fun h => by have := hρ.2.1; rw [h] at this; simp at this; linarith
      have hρ1 : 1 - ρ ≠ 0 := fun h => by
        have := congrArg Complex.re h; simp at this; linarith [hρ.2.2]
      rw [List.map_cons, List.prod_cons, List.map_cons, List.sum_cons, mul_add, Real.exp_add,
        ih (fun ρ' h => hl ρ' (List.mem_cons_of_mem _ h)) (List.nodup_cons.mp hnd).2]
      congr 1
      rw [Real.log_div (norm_ne_zero_iff.mpr hρ0) (norm_ne_zero_iff.mpr hρ1)]
      rw [show -2 * (Real.log ‖ρ‖ - Real.log ‖1 - ρ‖) =
        2 * Real.log ‖1 - ρ‖ - 2 * Real.log ‖ρ‖ by ring, Real.exp_sub,
        ← Real.log_rpow (norm_pos_iff.mpr hρ1), ← Real.log_rpow (norm_pos_iff.mpr hρ0),
        Real.exp_log (by positivity), Real.exp_log (by positivity)]
      norm_cast
  rw [← hprod]
  exact one_sub_prod_le_bdDistDiscrete_sq N hl hnd

end

end RHTower
