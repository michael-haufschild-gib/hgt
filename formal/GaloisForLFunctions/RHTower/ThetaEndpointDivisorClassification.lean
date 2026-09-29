import GaloisForLFunctions.RHTower.ThetaZeroDivisionRealization
import GaloisForLFunctions.HTGeometry.FiniteMeasureL1Duality
import GaloisForLFunctions.HTGeometry.PolynomialImagRaysLiouville

/-!
# Divisor-keeping theta-dominated sources: the finite-defect classification

Let `k` be the completed theta source, `F = XiC = k̂`, and `μ = k dx` the theta measure.

* Symmetries of the Xi divisor: orders of `F` agree at `z`, `-z`, `conj z`; zeros lie in the band
  `|Im z| < 5/2` and off the imaginary axis, so every nonreal zero has a quartet representative in
  the open first quadrant (`xiQuadrantZeros`); RH in the Fourier coordinate is the emptiness of that
  set.
* The off-line divisor list repeats each first-quadrant zero `α` and `conj α` with the multiplicity of
  `α`; its divisor polynomial `P(z) = ∏ (1 - z²/β²)` is even, real, positive on `ℝ`, nonvanishing off
  the band, of degree `4M`, and vanishes at each off-line zero exactly to the order of `F`.
* The real-zero jets `φ_{γ,j}(x) = ∂_t^j cos(tx)|_{t=γ} = Re((-ix)^j e^{-iγx})`; for a real even
  `k`-dominated source `v`, `(v̂)^{(j)}(γ) = ∫ φ_{γ,j} v`, so annihilating the jets at every positive
  real zero is keeping every real zero of `F` in `v̂`.
* **Finite-defect classification.**  With finitely many first-quadrant zeros, every real even
  `k`-dominated source `v` whose transform keeps the real zeros satisfies
  `v̂(z) P(z) = F(z) e(z²)` for a real polynomial `e` of degree at most `2M`: `E = P v̂ / F` is entire
  of order one, bounded by `C|P|` on the imaginary axis and by `3C|P| e^{(|Re z|/2) arctan(…)}` off
  the zero band, hence a polynomial of degree at most `4M` by the polynomial Liouville theorem on four
  rays; its evenness and reality are read off on the unit disc.
-/
open MeasureTheory Set Filter Topology Complex
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

/-! ## Symmetries of the Xi divisor -/

theorem iteratedDeriv_conj_comp_conj' (f : ℂ → ℂ) (n : ℕ) :
    iteratedDeriv n ((starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ)) =
      (starRingEnd ℂ) ∘ iteratedDeriv n f ∘ (starRingEnd ℂ) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iteratedDeriv_succ, iteratedDeriv_succ, ih, deriv_conj_conj]

theorem iteratedDeriv_XiC_starRingEnd (n : ℕ) (z : ℂ) :
    iteratedDeriv n XiC ((starRingEnd ℂ) z) = (starRingEnd ℂ) (iteratedDeriv n XiC z) := by
  have hreal : (starRingEnd ℂ) ∘ XiC ∘ (starRingEnd ℂ) = XiC := by
    funext w
    simp only [Function.comp_apply, XiC_conj, Complex.conj_conj]
  have h := congrFun (iteratedDeriv_conj_comp_conj' XiC n) ((starRingEnd ℂ) z)
  rw [hreal] at h
  simpa using h

theorem analyticOrderAt_XiC_starRingEnd (z : ℂ) :
    analyticOrderAt XiC ((starRingEnd ℂ) z) = analyticOrderAt XiC z := by
  refine ENat.eq_of_forall_natCast_le_iff fun n => ?_
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (XiC_differentiable.analyticAt _),
    natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (XiC_differentiable.analyticAt _)]
  simp only [iteratedDeriv_XiC_starRingEnd, map_eq_zero]

theorem analyticOrderAt_XiC_neg_eq (z : ℂ) : analyticOrderAt XiC (-z) = analyticOrderAt XiC z := by
  refine ENat.eq_of_forall_natCast_le_iff fun n => ?_
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (XiC_differentiable.analyticAt _),
    natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (XiC_differentiable.analyticAt _)]
  have hfun : XiC = fun w => XiC (-w) := funext fun w => (XiC_even w).symm
  have key : ∀ i w, iteratedDeriv i XiC w = (-1) ^ i * iteratedDeriv i XiC (-w) := by
    intro i w
    conv_lhs => rw [hfun]
    rw [iteratedDeriv_comp_neg, smul_eq_mul]
  constructor
  · intro h i hi
    rw [key i z, h i hi, mul_zero]
  · intro h i hi
    rw [key i (-z), neg_neg, h i hi, mul_zero]

theorem analyticOrderAt_XiC_ne_top_of_entire (z : ℂ) : analyticOrderAt XiC z ≠ ⊤ := by
  have hA : AnalyticOnNhd ℂ XiC univ := fun w _ => XiC_differentiable.analyticAt w
  have h0 : analyticOrderAt XiC 0 ≠ ⊤ := by
    rw [(XiC_differentiable.analyticAt 0).analyticOrderAt_eq_zero.2
      (XiC_ne_zero_of_norm_le_one (by simp))]
    exact ENat.zero_ne_top
  exact hA.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ 0)
    (mem_univ z) h0

theorem XiC_I_mul_ne_zero (y : ℝ) : XiC (I * y) ≠ 0 := by
  rw [XiC_I_mul]
  exact_mod_cast (thetaSourceLaplace_pos y).ne'

theorem XiC_ne_zero_of_band {z : ℂ} (hz : 5 / 2 ≤ |z.im|) : XiC z ≠ 0 := by
  intro h
  have h1 := thetaSourceLaplace_le_mul_norm_XiC hz
  rw [h, norm_zero, mul_zero] at h1
  linarith [thetaSourceLaplace_pos z.im]

theorem re_ne_zero_of_XiC_eq_zero {z : ℂ} (hz : XiC z = 0) : z.re ≠ 0 := by
  intro h
  apply XiC_I_mul_ne_zero z.im
  have : z = I * (z.im : ℂ) := by
    apply Complex.ext <;> simp [h]
  rw [← this]
  exact hz

/-- The zeros of `F = XiC` in the open first quadrant (one representative per quartet). -/
def xiQuadrantZeros : Set ℂ := {α | 0 < α.re ∧ 0 < α.im ∧ XiC α = 0}

/-- Every nonreal zero has a quartet representative in the first quadrant. -/
theorem exists_mem_xiQuadrantZeros {z : ℂ} (hz : XiC z = 0) (him : z.im ≠ 0) :
    ∃ α ∈ xiQuadrantZeros, α = z ∨ α = -z ∨ α = (starRingEnd ℂ) z ∨ α = -(starRingEnd ℂ) z := by
  have hre := re_ne_zero_of_XiC_eq_zero hz
  have hneg : XiC (-z) = 0 := by rw [XiC_even]; exact hz
  have hconj : XiC ((starRingEnd ℂ) z) = 0 := by rw [XiC_conj, hz, map_zero]
  have hnc : XiC (-(starRingEnd ℂ) z) = 0 := by rw [XiC_even]; exact hconj
  rcases lt_or_gt_of_ne hre with hr | hr <;> rcases lt_or_gt_of_ne him with hi | hi
  · exact ⟨-z, ⟨by simp; linarith, by simp; linarith, hneg⟩, by simp⟩
  · exact ⟨-(starRingEnd ℂ) z, ⟨by simp; linarith, by simp; linarith, hnc⟩, by simp⟩
  · exact ⟨(starRingEnd ℂ) z, ⟨by simp; linarith, by simp; linarith, hconj⟩, by simp⟩
  · exact ⟨z, ⟨hr, hi, hz⟩, by simp⟩

/-- **RH in the Fourier coordinate** is the absence of first-quadrant zeros. -/
theorem xiReal_iff_xiQuadrantZeros_eq_empty :
    (∀ z, XiC z = 0 → z.im = 0) ↔ xiQuadrantZeros = ∅ := by
  constructor
  · intro h
    ext α
    simp only [xiQuadrantZeros, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
    intro _ hi hz
    exact hi.ne' (h α hz)
  · intro h z hz
    by_contra him
    obtain ⟨α, hα, -⟩ := exists_mem_xiQuadrantZeros hz him
    rw [h] at hα
    exact hα

/-! ## The off-line divisor list -/

/-- The multiplicity of `α` as a zero of `F`, as a natural number. -/
def xiZeroMult (α : ℂ) : ℕ := (analyticOrderAt XiC α).toNat

theorem xiZeroMult_eq (α : ℂ) : (xiZeroMult α : ℕ∞) = analyticOrderAt XiC α :=
  ENat.coe_toNat (analyticOrderAt_XiC_ne_top_of_entire α)

theorem xiZeroMult_starRingEnd (α : ℂ) : xiZeroMult ((starRingEnd ℂ) α) = xiZeroMult α := by
  simp only [xiZeroMult, analyticOrderAt_XiC_starRingEnd]

theorem xiZeroMult_neg (α : ℂ) : xiZeroMult (-α) = xiZeroMult α := by
  simp only [xiZeroMult, analyticOrderAt_XiC_neg_eq]

/-- Each first-quadrant zero `α` of a list together with `conj α`, both with the multiplicity
of `α`. -/
def quadrantListOf : List ℂ → List ℂ
  | [] => []
  | α :: l => List.replicate (xiZeroMult α) α ++ List.replicate (xiZeroMult α) ((starRingEnd ℂ) α) ++
      quadrantListOf l

theorem mem_quadrantListOf {l : List ℂ} {β : ℂ} (hβ : β ∈ quadrantListOf l) :
    ∃ α ∈ l, β = α ∨ β = (starRingEnd ℂ) α := by
  induction l with
  | nil => simp [quadrantListOf] at hβ
  | cons α l ih =>
    simp only [quadrantListOf, List.mem_append, List.mem_replicate] at hβ
    rcases hβ with (⟨_, h⟩ | ⟨_, h⟩) | h
    · exact ⟨α, List.mem_cons_self, Or.inl h⟩
    · exact ⟨α, List.mem_cons_self, Or.inr h⟩
    · obtain ⟨a, ha, h'⟩ := ih h
      exact ⟨a, List.mem_cons_of_mem _ ha, h'⟩

theorem re_pos_of_mem_quadrantListOf {l : List ℂ} (hl : ∀ α ∈ l, α ∈ xiQuadrantZeros)
    {β : ℂ} (hβ : β ∈ quadrantListOf l) : 0 < β.re := by
  obtain ⟨α, hα, h⟩ := mem_quadrantListOf hβ
  rcases h with h | h <;> rw [h]
  · exact (hl α hα).1
  · simpa using (hl α hα).1

theorem XiC_eq_zero_of_mem_quadrantListOf {l : List ℂ} (hl : ∀ α ∈ l, α ∈ xiQuadrantZeros)
    {β : ℂ} (hβ : β ∈ quadrantListOf l) : XiC β = 0 := by
  obtain ⟨α, hα, h⟩ := mem_quadrantListOf hβ
  rcases h with h | h <;> rw [h]
  · exact (hl α hα).2.2
  · rw [XiC_conj, (hl α hα).2.2, map_zero]

theorem conj_ne_self_of_mem_xiQuadrantZeros {α : ℂ} (hα : α ∈ xiQuadrantZeros) :
    (starRingEnd ℂ) α ≠ α := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith [hα.2.1]

theorem count_replicate_eq (n : ℕ) (a b : ℂ) :
    (List.replicate n b).count a = if b = a then n else 0 := by
  simp [List.count_replicate]

/-- **Exact counts.**  In the list of a duplicate-free list of first-quadrant zeros, `β` occurs
`xiZeroMult β` times if `β` or `conj β` is listed, and otherwise not at all. -/
theorem count_quadrantListOf {l : List ℂ} (hl : ∀ α ∈ l, α ∈ xiQuadrantZeros) (hnd : l.Nodup)
    (β : ℂ) : (quadrantListOf l).count β =
      if β ∈ l ∨ (starRingEnd ℂ) β ∈ l then xiZeroMult β else 0 := by
  induction l with
  | nil => simp [quadrantListOf]
  | cons α l ih =>
    have hα := hl α List.mem_cons_self
    have hl' : ∀ a ∈ l, a ∈ xiQuadrantZeros := fun a ha => hl a (List.mem_cons_of_mem _ ha)
    have hnd' := hnd.of_cons
    have hαl : α ∉ l := (List.nodup_cons.1 hnd).1
    have hconj_notin : ∀ a : ℂ, 0 < a.im → (starRingEnd ℂ) a ∉ l := fun a ha hca => by
      have := (hl' _ hca).2.1
      simp at this
      linarith
    rw [quadrantListOf, List.count_append, List.count_append, count_replicate_eq,
      count_replicate_eq, ih hl' hnd']
    by_cases h1 : α = β
    · subst h1
      have hc : (starRingEnd ℂ) α ≠ α := conj_ne_self_of_mem_xiQuadrantZeros hα
      rw [if_pos rfl, if_neg hc, if_neg (not_or.2 ⟨hαl, hconj_notin α hα.2.1⟩),
        if_pos (Or.inl List.mem_cons_self)]
      simp
    · by_cases h2 : (starRingEnd ℂ) α = β
      · subst h2
        have hcc : (starRingEnd ℂ) ((starRingEnd ℂ) α) = α := Complex.conj_conj α
        rw [if_neg h1, if_pos rfl, hcc, if_neg (not_or.2 ⟨hconj_notin α hα.2.1, hαl⟩),
          if_pos (Or.inr List.mem_cons_self), xiZeroMult_starRingEnd]
        simp
      · have h1' : β ≠ α := fun h => h1 h.symm
        have h2' : (starRingEnd ℂ) β ≠ α := fun h => h2 (by rw [← h, Complex.conj_conj])
        rw [if_neg h1, if_neg h2, zero_add, zero_add]
        simp only [List.mem_cons, h1', h2', false_or]

theorem length_quadrantListOf (l : List ℂ) :
    (quadrantListOf l).length = (l.map fun α => 2 * xiZeroMult α).sum := by
  induction l with
  | nil => simp [quadrantListOf]
  | cons α l ih => simp [quadrantListOf, ih]; ring

theorem thetaDivisionList_quadrantListOf {l : List ℂ} (hl : ∀ α ∈ l, α ∈ xiQuadrantZeros)
    (hnd : l.Nodup) : ThetaDivisionList (quadrantListOf l) := by
  refine ⟨fun β hβ => re_pos_of_mem_quadrantListOf hl hβ, fun β => ?_⟩
  rw [count_quadrantListOf hl hnd]
  split_ifs
  · exact (xiZeroMult_eq β).le
  · simp

/-! ## The off-line divisor polynomial -/

theorem listDivisor_append (L₁ L₂ : List ℂ) (z : ℂ) :
    listDivisor (L₁ ++ L₂) z = listDivisor L₁ z * listDivisor L₂ z := by
  simp [listDivisor, List.prod_append]

theorem listDivisor_replicate (m : ℕ) (β z : ℂ) :
    listDivisor (List.replicate m β) z = (1 - z ^ 2 / β ^ 2) ^ m := by
  simp [listDivisor, List.map_replicate, List.prod_replicate]

theorem listDivisor_quadrantListOf_cons (α : ℂ) (l : List ℂ) (z : ℂ) :
    listDivisor (quadrantListOf (α :: l)) z =
      ((1 - z ^ 2 / α ^ 2) * (1 - z ^ 2 / (starRingEnd ℂ) α ^ 2)) ^ xiZeroMult α *
        listDivisor (quadrantListOf l) z := by
  rw [quadrantListOf, listDivisor_append, listDivisor_append, listDivisor_replicate,
    listDivisor_replicate, mul_pow]

theorem listDivisor_quadrantListOf_conj (l : List ℂ) (z : ℂ) :
    (starRingEnd ℂ) (listDivisor (quadrantListOf l) ((starRingEnd ℂ) z)) =
      listDivisor (quadrantListOf l) z := by
  induction l with
  | nil => simp [quadrantListOf, listDivisor_nil]
  | cons α l ih =>
    rw [listDivisor_quadrantListOf_cons, listDivisor_quadrantListOf_cons, map_mul, ih, map_pow]
    congr 2
    simp only [map_mul, map_sub, map_one, map_div₀, map_pow, Complex.conj_conj]
    ring

/-- On the real axis the off-line divisor polynomial is a positive real number. -/
theorem listDivisor_quadrantListOf_ofReal {l : List ℂ} (hl : ∀ α ∈ l, α ∈ xiQuadrantZeros)
    (x : ℝ) : ∃ r : ℝ, 0 < r ∧ listDivisor (quadrantListOf l) x = r := by
  induction l with
  | nil => exact ⟨1, one_pos, by simp [quadrantListOf, listDivisor_nil]⟩
  | cons α l ih =>
    obtain ⟨r, hr, hrx⟩ := ih fun a ha => hl a (List.mem_cons_of_mem _ ha)
    have hα := hl α List.mem_cons_self
    set w : ℂ := 1 - (x : ℂ) ^ 2 / α ^ 2
    have hw : w ≠ 0 := by
      intro h0
      have hα0 : α ≠ 0 := fun h => by rw [h] at hα; simp [xiQuadrantZeros] at hα
      have h1 : α ^ 2 = (x : ℂ) ^ 2 := by
        have := sub_eq_zero.1 h0
        field_simp at this
        exact this
      have h2 := congrArg Complex.im h1
      simp only [sq, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        zero_mul, add_zero] at h2
      have := mul_pos hα.1 hα.2.1
      linarith
    have hpair : (1 - (x : ℂ) ^ 2 / α ^ 2) * (1 - (x : ℂ) ^ 2 / (starRingEnd ℂ) α ^ 2) =
        (Complex.normSq w : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]
      simp only [w, map_sub, map_one, map_div₀, map_pow, Complex.conj_ofReal]
      ring
    refine ⟨Complex.normSq w ^ xiZeroMult α * r, mul_pos (pow_pos (Complex.normSq_pos.2 hw) _) hr, ?_⟩
    rw [listDivisor_quadrantListOf_cons, hpair, hrx]
    push_cast
    ring

theorem listDivisor_zero (L : List ℂ) : listDivisor L 0 = 1 := by
  induction L with
  | nil => exact listDivisor_nil 0
  | cons β L ih => rw [listDivisor_cons, ih]; simp

theorem exists_mem_of_listDivisor_eq_zero {L : List ℂ} {z : ℂ} (h : listDivisor L z = 0) :
    ∃ β ∈ L, z = β ∨ z = -β := by
  induction L with
  | nil => simp [listDivisor_nil] at h
  | cons β L ih =>
    rw [listDivisor_cons, mul_eq_zero] at h
    rcases h with h | h
    · have hβ0 : β ≠ 0 := by
        rintro rfl
        simp at h
      have hsq : z ^ 2 = β ^ 2 := by
        have := sub_eq_zero.1 h
        field_simp at this
        exact this.symm
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h' | h'
      · exact ⟨β, List.mem_cons_self, Or.inl h'⟩
      · exact ⟨β, List.mem_cons_self, Or.inr h'⟩
    · obtain ⟨b, hb, h'⟩ := ih h
      exact ⟨b, List.mem_cons_of_mem _ hb, h'⟩

/-- The off-line divisor polynomial does not vanish off the zero band. -/
theorem listDivisor_quadrantListOf_ne_zero {l : List ℂ} (hl : ∀ α ∈ l, α ∈ xiQuadrantZeros)
    {z : ℂ} (hz : 5 / 2 ≤ |z.im|) : listDivisor (quadrantListOf l) z ≠ 0 := by
  intro h
  obtain ⟨β, hβ, h' | h'⟩ := exists_mem_of_listDivisor_eq_zero h
  · exact XiC_ne_zero_of_band hz (h' ▸ XiC_eq_zero_of_mem_quadrantListOf hl hβ)
  · have : XiC z = 0 := by rw [h', XiC_even]; exact XiC_eq_zero_of_mem_quadrantListOf hl hβ
    exact XiC_ne_zero_of_band hz this

theorem norm_listDivisor_le (L : List ℂ) (z : ℂ) :
    ‖listDivisor L z‖ ≤ (L.map fun β => 1 + 1 / ‖β‖ ^ 2).prod * (1 + ‖z‖) ^ (2 * L.length) := by
  induction L with
  | nil => simp [listDivisor_nil]
  | cons β L ih =>
    rw [listDivisor_cons, norm_mul, List.map_cons, List.prod_cons, List.length_cons,
      show 2 * (L.length + 1) = 2 + 2 * L.length by ring, pow_add]
    have h1 : ‖1 - z ^ 2 / β ^ 2‖ ≤ (1 + 1 / ‖β‖ ^ 2) * (1 + ‖z‖) ^ 2 := by
      calc ‖1 - z ^ 2 / β ^ 2‖ ≤ 1 + ‖z‖ ^ 2 / ‖β‖ ^ 2 := by
            refine (norm_sub_le _ _).trans ?_
            rw [norm_one, norm_div, norm_pow, norm_pow]
        _ ≤ (1 + 1 / ‖β‖ ^ 2) * (1 + ‖z‖) ^ 2 := by
            have hz := norm_nonneg z
            rw [div_eq_mul_one_div]
            have hb : 0 ≤ 1 / ‖β‖ ^ 2 := by positivity
            nlinarith [mul_le_mul_of_nonneg_left (by nlinarith : ‖z‖ ^ 2 ≤ (1 + ‖z‖) ^ 2) hb]
    have h0 : 0 ≤ (L.map fun β => 1 + 1 / ‖β‖ ^ 2).prod :=
      List.prod_nonneg fun a ha => by
        obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha
        positivity
    calc ‖1 - z ^ 2 / β ^ 2‖ * ‖listDivisor L z‖ ≤
          ((1 + 1 / ‖β‖ ^ 2) * (1 + ‖z‖) ^ 2) *
            ((L.map fun β => 1 + 1 / ‖β‖ ^ 2).prod * (1 + ‖z‖) ^ (2 * L.length)) :=
          mul_le_mul h1 ih (norm_nonneg _) (by positivity)
      _ = _ := by ring

/-! ## The theta measure -/

/-- The density `k` of the theta measure. -/
def thetaSourceDensity (x : ℝ) : ℝ≥0 := (thetaCuspFullSource x).toNNReal

theorem measurable_thetaSourceDensity : Measurable thetaSourceDensity :=
  contDiff_thetaCuspFullSource.continuous.measurable.real_toNNReal

theorem thetaSourceDensity_coe (x : ℝ) : (thetaSourceDensity x : ℝ) = thetaCuspFullSource x :=
  Real.coe_toNNReal _ (thetaCuspFullSource_pos x).le

theorem thetaSourceDensity_neg (x : ℝ) : thetaSourceDensity (-x) = thetaSourceDensity x := by
  simp only [thetaSourceDensity, thetaCuspFullSource_neg]

/-- The theta measure `dμ = k(x) dx`. -/
def thetaSourceMeasure : Measure ℝ := volume.withDensity fun x => (thetaSourceDensity x : ℝ≥0∞)

instance : IsFiniteMeasure thetaSourceMeasure := by
  have h : HasFiniteIntegral thetaCuspFullSource :=
    ((HedenmalmThetaSource.integrable_exp_mul_thetaCuspFullSource 0).congr
      (Eventually.of_forall fun x => by simp)).hasFiniteIntegral
  exact isFiniteMeasure_withDensity_ofReal h

theorem integral_thetaSourceMeasure (g : ℝ → ℝ) :
    ∫ x, g x ∂thetaSourceMeasure = ∫ x, thetaCuspFullSource x * g x := by
  rw [thetaSourceMeasure, integral_withDensity_eq_integral_smul measurable_thetaSourceDensity]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [NNReal.smul_def, smul_eq_mul, thetaSourceDensity_coe]

theorem integrable_thetaSourceMeasure_iff {g : ℝ → ℝ} :
    Integrable g thetaSourceMeasure ↔ Integrable fun x => thetaCuspFullSource x * g x := by
  rw [thetaSourceMeasure, integrable_withDensity_iff_integrable_smul measurable_thetaSourceDensity]
  simp only [NNReal.smul_def, smul_eq_mul, thetaSourceDensity_coe]

theorem ae_thetaSourceMeasure_iff {p : ℝ → Prop} : (∀ᵐ x ∂thetaSourceMeasure, p x) ↔ ∀ᵐ x, p x := by
  rw [thetaSourceMeasure, ae_withDensity_iff measurable_thetaSourceDensity.coe_nnreal_ennreal]
  constructor
  · intro h
    filter_upwards [h] with x hx
    refine hx ?_
    simp [thetaSourceDensity, thetaCuspFullSource_pos x]
  · intro h
    filter_upwards [h] with x hx _
    exact hx

instance : thetaSourceMeasure.IsNegInvariant := by
  refine ⟨Measure.ext fun A hA => ?_⟩
  rw [Measure.neg_apply, thetaSourceMeasure, withDensity_apply _ hA, withDensity_apply _ hA.neg]
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.neg ℝ).measurableEmbedding (fun x => (thetaSourceDensity x : ℝ≥0∞)) A
  rw [show Neg.neg ⁻¹' A = -A from rfl] at h
  simp only [thetaSourceDensity_neg] at h
  exact h

/-! ## The real-zero jets -/

/-- The real-zero jet `φ_{γ,j}(x) = Re((-ix)^j e^{-iγx})`. -/
def thetaCosJet (γ : ℝ) (j : ℕ) (x : ℝ) : ℝ := ((-(I * x)) ^ j * cexp (-(I * γ * x))).re

/-- The jet is the `j`-th `t`-derivative of `cos(tx)` at `t = γ`. -/
theorem thetaCosJet_eq_iteratedDeriv (γ : ℝ) (j : ℕ) (x : ℝ) :
    thetaCosJet γ j x = iteratedDeriv j (fun t : ℝ => Real.cos (t * x)) γ := by
  have hform : ∀ (n : ℕ) (s : ℝ), thetaCosJet s n x = ((-(I * x)) ^ n * cexp (-(I * x) * s)).re :=
    fun n s => by unfold thetaCosJet; ring_nf
  have hderiv : ∀ n : ℕ, ∀ t : ℝ, HasDerivAt (fun s : ℝ => thetaCosJet s n x)
      (thetaCosJet t (n + 1) x) t := by
    intro n t
    have h : HasDerivAt (fun w : ℂ => (-(I * x)) ^ n * cexp (-(I * x) * w))
        ((-(I * x)) ^ (n + 1) * cexp (-(I * x) * t)) (t : ℂ) := by
      have h1 := (Complex.hasDerivAt_exp (-(I * x) * t)).comp (t : ℂ)
        ((hasDerivAt_id (t : ℂ)).const_mul (-(I * x)))
      have h2 := h1.const_mul ((-(I * x)) ^ n)
      exact h2.congr_deriv (by ring)
    rw [show (fun s : ℝ => thetaCosJet s n x) =
      fun s : ℝ => ((-(I * x)) ^ n * cexp (-(I * x) * s)).re from funext (hform n), hform (n + 1)]
    exact h.real_of_complex
  have hfun : ∀ n : ℕ, iteratedDeriv n (fun t : ℝ => Real.cos (t * x)) = fun t => thetaCosJet t n x := by
    intro n
    induction n with
    | zero =>
      funext t
      simp only [iteratedDeriv_zero, thetaCosJet, pow_zero, one_mul]
      rw [show -(I * t * x) = ((-(t * x) : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_ofReal_mul_I_re,
        Real.cos_neg]
    | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      exact (hderiv n t).deriv
  rw [hfun j]

theorem jet_neg_eq_conj (γ : ℝ) (j : ℕ) (x : ℝ) :
    (-(I * ((-x : ℝ) : ℂ))) ^ j * cexp (-(I * γ * ((-x : ℝ) : ℂ))) =
      (starRingEnd ℂ) ((-(I * x)) ^ j * cexp (-(I * γ * x))) := by
  have e1 : -(I * ((-x : ℝ) : ℂ)) = (starRingEnd ℂ) (-(I * x)) := by
    simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]; ring
  have e2 : -(I * γ * ((-x : ℝ) : ℂ)) = (starRingEnd ℂ) (-(I * γ * x)) := by
    simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]; ring
  rw [e1, e2, ← map_pow, Complex.exp_conj, ← map_mul]

theorem thetaCosJet_neg (γ : ℝ) (j : ℕ) (x : ℝ) : thetaCosJet γ j (-x) = thetaCosJet γ j x := by
  unfold thetaCosJet
  rw [jet_neg_eq_conj, Complex.conj_re]

theorem abs_thetaCosJet_le (γ : ℝ) (j : ℕ) (x : ℝ) : |thetaCosJet γ j x| ≤ |x| ^ j := by
  unfold thetaCosJet
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, norm_pow, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs]
  have : ‖cexp (-(I * γ * x))‖ = 1 := by
    rw [show -(I * γ * x) = ((-(γ * x) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  rw [this, mul_one]

theorem continuous_thetaCosJet (γ : ℝ) (j : ℕ) : Continuous (thetaCosJet γ j) := by
  unfold thetaCosJet
  fun_prop

/-- The imaginary companion of the jet is odd. -/
theorem im_jet_neg (γ : ℝ) (j : ℕ) (x : ℝ) :
    ((-(I * ((-x : ℝ) : ℂ))) ^ j * cexp (-(I * γ * ((-x : ℝ) : ℂ)))).im =
      -((-(I * x)) ^ j * cexp (-(I * γ * x))).im := by
  rw [jet_neg_eq_conj, Complex.conj_im]

/-! ## Fourier jets of real even sources -/

theorem MeasurableMomentSource.mul_negIX {f : ℝ → ℂ} (hf : MeasurableMomentSource f) :
    MeasurableMomentSource fun x => -(I * x) * f x := by
  refine ⟨(by fun_prop : Continuous fun x : ℝ => -(I * (x : ℂ))).aestronglyMeasurable.mul
    hf.aestronglyMeasurable, fun c => ?_⟩
  refine (hf.moment (c + 1)).mono' ((by fun_prop : Continuous fun x : ℝ =>
    Real.exp (c * |x|)).aestronglyMeasurable.mul ((by fun_prop : Continuous fun x : ℝ =>
      -(I * (x : ℂ))).aestronglyMeasurable.mul hf.aestronglyMeasurable).norm)
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (by positivity), norm_mul, norm_neg, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs]
  have hx : |x| ≤ Real.exp |x| := by linarith [Real.add_one_le_exp |x|]
  calc Real.exp (c * |x|) * (|x| * ‖f x‖) ≤ Real.exp (c * |x|) * (Real.exp |x| * ‖f x‖) := by
        gcongr
    _ = Real.exp ((c + 1) * |x|) * ‖f x‖ := by rw [add_mul, one_mul, Real.exp_add]; ring

theorem MeasurableMomentSource.deriv_sourceTransform {f : ℝ → ℂ} (hf : MeasurableMomentSource f) :
    deriv (sourceTransform f) = sourceTransform fun x => -(I * x) * f x := by
  funext w
  rw [(hf.hasDerivAt_sourceTransform w).deriv, sourceTransform]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  ring

theorem MeasurableMomentSource.iteratedDeriv_sourceTransform {f : ℝ → ℂ}
    (hf : MeasurableMomentSource f) (j : ℕ) :
    iteratedDeriv j (sourceTransform f) = sourceTransform fun x => (-(I * x)) ^ j * f x := by
  induction j generalizing f with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ', hf.deriv_sourceTransform, ih hf.mul_negIX]
    congr 1
    funext x
    ring

theorem integral_odd_mul_even_eq_zero {g v : ℝ → ℝ} (hg : ∀ x, g (-x) = -g x)
    (hv : ∀ x, v (-x) = v x) : ∫ x, g x * v x = 0 := by
  have h := integral_neg_eq_self (fun x => g x * v x) volume
  simp only [hg, hv, neg_mul, integral_neg] at h
  linarith

/-- **Jets of the transform for moment sources.**  For a real even source `v` with every exponential
moment, `(v̂)^{(j)}(γ) = ∫ φ_{γ,j} v` at real `γ`. -/
theorem iteratedDeriv_sourceTransform_ofReal_of_moment {v : ℝ → ℝ}
    (hms : MeasurableMomentSource fun x => (v x : ℂ)) (heven : ∀ x, v (-x) = v x) (γ : ℝ)
    (j : ℕ) : iteratedDeriv j (sourceTransform fun x => (v x : ℂ)) γ =
      ((∫ x, thetaCosJet γ j x * v x : ℝ) : ℂ) := by
  have hmsj : MeasurableMomentSource fun x => (-(I * x)) ^ j * (v x : ℂ) := by
    induction j with
    | zero => simpa using hms
    | succ j ih =>
      have := ih.mul_negIX
      refine ⟨?_, ?_⟩
      · exact this.aestronglyMeasurable.congr (Eventually.of_forall fun x => by simp only; ring)
      · intro c
        exact (this.moment c).congr (Eventually.of_forall fun x => by simp only; ring_nf)
  rw [hms.iteratedDeriv_sourceTransform j]
  set w : ℝ → ℂ := fun x => ((-(I * x)) ^ j * cexp (-(I * γ * x))) * (v x : ℂ)
  have hw : Integrable w := (hmsj.integrable_cexp γ).congr (Eventually.of_forall fun x => by
    simp only [w]; ring_nf)
  have hST : sourceTransform (fun x => (-(I * x)) ^ j * (v x : ℂ)) γ = ∫ x, w x := by
    unfold sourceTransform
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [w]
    ring_nf
  rw [hST]
  apply Complex.ext
  · have h1 := integral_re hw
    simp only [RCLike.re_to_complex] at h1
    rw [← h1, Complex.ofReal_re]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [w, Complex.re_mul_ofReal, thetaCosJet]
  · have h1 := integral_im hw
    simp only [RCLike.im_to_complex] at h1
    rw [← h1, Complex.ofReal_im]
    set ψ : ℝ → ℝ := fun x => ((-(I * (x : ℂ))) ^ j * cexp (-(I * γ * (x : ℂ)))).im
    have h : ∫ x, (w x).im = ∫ x, ψ x * v x := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [w, ψ, Complex.im_mul_ofReal]
    rw [h]
    exact integral_odd_mul_even_eq_zero (fun x => im_jet_neg γ j x) heven

/-- **Jets of the transform.**  For a real even source `v` with `|v| ≤ C k`, the `j`-th derivative
of `H = v̂` at a real point `γ` is the real number `∫ φ_{γ,j} v`. -/
theorem iteratedDeriv_sourceTransform_ofReal {v : ℝ → ℝ} (hv : AEStronglyMeasurable v) {C : ℝ}
    (hC : ∀ x, |v x| ≤ C * thetaCuspFullSource x) (heven : ∀ x, v (-x) = v x) (γ : ℝ) (j : ℕ) :
    iteratedDeriv j (sourceTransform fun x => (v x : ℂ)) γ =
      ((∫ x, thetaCosJet γ j x * v x : ℝ) : ℂ) :=
  iteratedDeriv_sourceTransform_ofReal_of_moment
    (measurableMomentSource_of_le (Complex.continuous_ofReal.comp_aestronglyMeasurable hv)
      fun x => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hC x) heven γ j

/-- The orders of an even entire function at `z` and `-z` agree. -/
theorem analyticOrderAt_neg_of_even {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (heven : ∀ z, H (-z) = H z) (z : ℂ) : analyticOrderAt H (-z) = analyticOrderAt H z := by
  refine ENat.eq_of_forall_natCast_le_iff fun n => ?_
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hH.analyticAt _),
    natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hH.analyticAt _)]
  have hfun : H = fun w => H (-w) := funext fun w => (heven w).symm
  have key : ∀ i w, iteratedDeriv i H w = (-1) ^ i * iteratedDeriv i H (-w) := by
    intro i w
    conv_lhs => rw [hfun]
    rw [iteratedDeriv_comp_neg, smul_eq_mul]
  constructor
  · intro h i hi
    rw [key i z, h i hi, mul_zero]
  · intro h i hi
    rw [key i (-z), neg_neg, h i hi, mul_zero]

theorem xiZeroMult_eq_zero_of_ne {z : ℂ} (h : XiC z ≠ 0) : xiZeroMult z = 0 := by
  simp [xiZeroMult, (XiC_differentiable.analyticAt z).analyticOrderAt_eq_zero.2 h]

/-- `H` keeps every real zero of `F` with at least its multiplicity. -/
def KeepsRealZeros (H : ℂ → ℂ) : Prop := ∀ γ : ℝ, analyticOrderAt XiC γ ≤ analyticOrderAt H γ

/-- **Annihilating the jets is keeping the real zeros.** -/
theorem keepsRealZeros_iff_jets {v : ℝ → ℝ} (hv : AEStronglyMeasurable v) {C : ℝ}
    (hC : ∀ x, |v x| ≤ C * thetaCuspFullSource x) (heven : ∀ x, v (-x) = v x) :
    KeepsRealZeros (sourceTransform fun x => (v x : ℂ)) ↔
      ∀ γ : ℝ, 0 < γ → XiC γ = 0 → ∀ j : ℕ, (j : ℕ∞) < analyticOrderAt XiC γ →
        ∫ x, thetaCosJet γ j x * v x = 0 := by
  have hms : MeasurableMomentSource fun x => (v x : ℂ) :=
    measurableMomentSource_of_le (Complex.continuous_ofReal.comp_aestronglyMeasurable hv)
      fun x => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hC x
  have hHd := hms.differentiable_sourceTransform
  have hHeven : ∀ z, sourceTransform (fun x => (v x : ℂ)) (-z) =
      sourceTransform (fun x => (v x : ℂ)) z :=
    sourceTransform_neg_eq_of_even fun x => by simp only [heven]
  have hjet : ∀ (γ : ℝ) (n : ℕ), ((n : ℕ∞) ≤ analyticOrderAt (sourceTransform fun x => (v x : ℂ)) γ ↔
      ∀ j < n, ∫ x, thetaCosJet γ j x * v x = 0) := by
    intro γ n
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hHd.analyticAt _)]
    simp only [iteratedDeriv_sourceTransform_ofReal hv hC heven, Complex.ofReal_eq_zero]
  constructor
  · intro h γ hγ _ j hj
    have hle := h γ
    rw [← xiZeroMult_eq] at hle hj
    exact (hjet γ (xiZeroMult γ)).1 hle j (by exact_mod_cast hj)
  · intro h γ
    rw [← xiZeroMult_eq]
    rcases lt_trichotomy γ 0 with hγ | hγ | hγ
    · have h1 : xiZeroMult (γ : ℂ) = xiZeroMult ((-γ : ℝ) : ℂ) := by
        rw [Complex.ofReal_neg, xiZeroMult_neg]
      rw [h1, show ((γ : ℝ) : ℂ) = -((-γ : ℝ) : ℂ) by push_cast; ring,
        analyticOrderAt_neg_of_even hHd hHeven]
      by_cases hz : XiC ((-γ : ℝ) : ℂ) = 0
      · refine (hjet (-γ) _).2 fun j hj => h (-γ) (by linarith) hz j ?_
        rw [← xiZeroMult_eq]; exact_mod_cast hj
      · rw [xiZeroMult_eq_zero_of_ne hz]; simp
    · subst hγ
      have : XiC ((0 : ℝ) : ℂ) ≠ 0 := XiC_ne_zero_of_norm_le_one (by simp)
      rw [xiZeroMult_eq_zero_of_ne this]; simp
    · by_cases hz : XiC (γ : ℂ) = 0
      · refine (hjet γ _).2 fun j hj => h γ hγ hz j ?_
        rw [← xiZeroMult_eq]; exact_mod_cast hj
      · rw [xiZeroMult_eq_zero_of_ne hz]; simp

/-! ## Classification of divisor-keeping sources -/

/-- A polynomial vanishing on the closed unit disc has zero coefficients. -/
theorem coeff_eq_zero_of_sum_eq_zero_on_disc {c : ℕ → ℂ} {n : ℕ}
    (h : ∀ z : ℂ, ‖z‖ ≤ 1 → ∑ i ∈ Finset.range n, c i * z ^ i = 0) :
    ∀ i < n, c i = 0 := by
  set q : Polynomial ℂ := ∑ i ∈ Finset.range n, Polynomial.C (c i) * Polynomial.X ^ i
  have heval : ∀ z, q.eval z = ∑ i ∈ Finset.range n, c i * z ^ i := fun z => by
    simp [q, Polynomial.eval_finsetSum]
  have hq : q = 0 := by
    refine Polynomial.eq_of_infinite_eval_eq q 0 ?_
    refine ((Set.Icc_infinite (zero_lt_one' ℝ)).image Complex.ofReal_injective.injOn).mono ?_
    rintro _ ⟨t, ht, rfl⟩
    simp only [mem_setOf_eq, Polynomial.eval_zero, heval]
    exact h _ (by rw [Complex.norm_real, Real.norm_of_nonneg ht.1]; exact ht.2)
  intro i hi
  have := congrArg (fun p : Polynomial ℂ => p.coeff i) hq
  simp only [q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_zero] at this
  rwa [Finset.sum_eq_single i (fun b _ hb => if_neg (Ne.symm hb))
    (fun h' => absurd (Finset.mem_range.2 hi) h'), if_pos rfl] at this

theorem sum_range_two_mul_add_one {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ Finset.range (2 * n + 1), f i =
      ∑ j ∈ Finset.range (n + 1), f (2 * j) + ∑ j ∈ Finset.range n, f (2 * j + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring, Finset.sum_range_succ f (2 * n + 1 + 1),
      Finset.sum_range_succ f (2 * n + 1), ih,
      Finset.sum_range_succ (fun j => f (2 * j)) (n + 1),
      Finset.sum_range_succ (fun j => f (2 * j + 1)) n, show 2 * n + 1 + 1 = 2 * (n + 1) by ring]
    abel

theorem xiShape_nonneg (z : ℂ) : 0 ≤ (1 + ‖z‖) * Real.log (2 + ‖z‖) := by
  have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + ‖z‖ by linarith [norm_nonneg z]); positivity

theorem one_add_norm_pow_le_exp_shape (N : ℕ) (z : ℂ) :
    (1 + ‖z‖) ^ N ≤ Real.exp (N * ((1 + ‖z‖) * Real.log (2 + ‖z‖))) := by
  rw [← Real.exp_log (by positivity : (0 : ℝ) < (1 + ‖z‖) ^ N), Real.log_pow]
  refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg N))
  have hl1 : Real.log (1 + ‖z‖) ≤ Real.log (2 + ‖z‖) :=
    Real.log_le_log (by positivity) (by linarith)
  have hl0 : 0 ≤ Real.log (2 + ‖z‖) := Real.log_nonneg (by linarith [norm_nonneg z])
  nlinarith [norm_nonneg z]

section Classification

variable (hfin : xiQuadrantZeros.Finite)

/-- The off-line divisor list of all first-quadrant zeros. -/
def xiOffLineList : List ℂ := quadrantListOf hfin.toFinset.toList

theorem mem_xiOffLineList_toList {α : ℂ} (hα : α ∈ hfin.toFinset.toList) : α ∈ xiQuadrantZeros :=
  hfin.mem_toFinset.1 (Finset.mem_toList.1 hα)

include hfin in
theorem nodup_xiOffLine_toList : hfin.toFinset.toList.Nodup := Finset.nodup_toList _

theorem thetaDivisionList_xiOffLineList : ThetaDivisionList (xiOffLineList hfin) :=
  thetaDivisionList_quadrantListOf (fun _ => mem_xiOffLineList_toList hfin) (nodup_xiOffLine_toList hfin)

/-- The off-line divisor polynomial `P(z)`: zeros exactly the nonreal zeros of `F`, with
multiplicity. -/
def xiOffLineDivisor (z : ℂ) : ℂ := listDivisor (xiOffLineList hfin) z

theorem analyticOrderAt_xiOffLineDivisor {z : ℂ} (hz : XiC z = 0) (him : z.im ≠ 0)
    (hre : 0 < z.re) : analyticOrderAt XiC z ≤ analyticOrderAt (xiOffLineDivisor hfin) z := by
  have hl := fun α (hα : α ∈ hfin.toFinset.toList) => mem_xiOffLineList_toList hfin hα
  show analyticOrderAt XiC z ≤ analyticOrderAt (listDivisor (quadrantListOf hfin.toFinset.toList)) z
  rw [analyticOrderAt_listDivisor hre _ (fun β hβ => re_pos_of_mem_quadrantListOf hl hβ),
    count_quadrantListOf hl (nodup_xiOffLine_toList hfin), if_pos, ← xiZeroMult_eq]
  rcases lt_or_gt_of_ne him with h | h
  · right
    refine (Finset.mem_toList).2 (hfin.mem_toFinset.2 ⟨by simpa using hre, by simpa using h, ?_⟩)
    rw [XiC_conj, hz, map_zero]
  · left
    exact (Finset.mem_toList).2 (hfin.mem_toFinset.2 ⟨hre, h, hz⟩)

theorem xiOffLineDivisor_neg (z : ℂ) : xiOffLineDivisor hfin (-z) = xiOffLineDivisor hfin z :=
  listDivisor_neg _ z

theorem differentiable_xiOffLineDivisor : Differentiable ℂ (xiOffLineDivisor hfin) :=
  differentiable_listDivisor _

/-- **Divisor containment.**  If `H` keeps the real zeros, `F` divides `P H`. -/
theorem analyticOrderAt_XiC_le_mul {H : ℂ → ℂ} (hHd : Differentiable ℂ H)
    (hkeep : KeepsRealZeros H) (z : ℂ) :
    analyticOrderAt XiC z ≤ analyticOrderAt (fun w => xiOffLineDivisor hfin w * H w) z := by
  have hPd := differentiable_xiOffLineDivisor hfin
  have hmul : ∀ w, analyticOrderAt (fun w => xiOffLineDivisor hfin w * H w) w =
      analyticOrderAt (xiOffLineDivisor hfin) w + analyticOrderAt H w := fun w =>
    analyticOrderAt_mul (hPd.analyticAt w) (hHd.analyticAt w)
  by_cases hz : XiC z = 0
  · by_cases him : z.im = 0
    · have hzr : z = (z.re : ℂ) := by apply Complex.ext <;> simp [him]
      rw [hmul, hzr]
      exact (hkeep z.re).trans le_add_self
    · have hre := re_ne_zero_of_XiC_eq_zero hz
      rcases lt_or_gt_of_ne hre with h | h
      · have hneg := analyticOrderAt_xiOffLineDivisor hfin (z := -z) (by rw [XiC_even]; exact hz)
          (by simpa using him) (by simpa using h)
        rw [analyticOrderAt_XiC_neg_eq] at hneg
        have hPe : ∀ w, xiOffLineDivisor hfin (-w) = xiOffLineDivisor hfin w :=
          xiOffLineDivisor_neg hfin
        rw [analyticOrderAt_neg_of_even hPd hPe] at hneg
        rw [hmul]
        exact hneg.trans le_self_add
      · rw [hmul]
        exact (analyticOrderAt_xiOffLineDivisor hfin hz him h).trans le_self_add
  · rw [(XiC_differentiable.analyticAt z).analyticOrderAt_eq_zero.2 hz]
    exact zero_le

theorem sourceTransform_ofReal_conj {v : ℝ → ℝ} (heven : ∀ x, v (-x) = v x) (z : ℂ) :
    (starRingEnd ℂ) (sourceTransform (fun x => (v x : ℂ)) ((starRingEnd ℂ) z)) =
      sourceTransform (fun x => (v x : ℂ)) z := by
  have h := sourceTransform_conj_comp (u := fun x => (v x : ℂ)) z
  simp only [Complex.conj_ofReal] at h
  rw [h, sourceTransform_neg_eq_of_even (fun x => by simp only [heven])]

/-- **Finite-defect classification.**  If `F` has finitely many first-quadrant zeros, every real
even source `v` with `|v| ≤ C k` whose transform keeps the real zeros of `F` satisfies
`v̂(z) P(z) = F(z) e(z²)` for a real polynomial `e` of degree at most `2M`, where `P` is the off-line
divisor polynomial of degree `4M`.  The quotient `E = P v̂ / F` is entire with an order-one envelope,
polynomially bounded on the imaginary axis and on rays near it, hence a polynomial; evenness and
reality are read off on the unit disc, where `F` does not vanish. -/
theorem exists_realPolynomial_of_keepsRealZeros {v : ℝ → ℝ} (hv : AEStronglyMeasurable v) {C : ℝ}
    (hC : ∀ x, |v x| ≤ C * thetaCuspFullSource x) (heven : ∀ x, v (-x) = v x)
    (hkeep : KeepsRealZeros (sourceTransform fun x => (v x : ℂ))) :
    ∃ e : Polynomial ℝ, e.natDegree ≤ (xiOffLineList hfin).length ∧
      ∀ z, sourceTransform (fun x => (v x : ℂ)) z * xiOffLineDivisor hfin z =
        XiC z * (e.map (algebraMap ℝ ℂ)).eval (z ^ 2) := by
  set H := sourceTransform fun x => (v x : ℂ) with hHdef
  set P := xiOffLineDivisor hfin with hPdef
  set n := (xiOffLineList hfin).length
  set N := 2 * n with hNdef
  have hCv : ∀ x, ‖(v x : ℂ)‖ ≤ C * thetaCuspFullSource x := fun x => by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hC x
  have hC0 : 0 ≤ C :=
    nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hC 0)) (thetaCuspFullSource_pos 0)
  have hms := measurableMomentSource_of_le
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hv) hCv
  have hHd : Differentiable ℂ H := hms.differentiable_sourceTransform
  have hHeven : ∀ z, H (-z) = H z := sourceTransform_neg_eq_of_even fun x => by simp only [heven]
  have hHconj : ∀ z, (starRingEnd ℂ) (H ((starRingEnd ℂ) z)) = H z :=
    sourceTransform_ofReal_conj heven
  have hPd : Differentiable ℂ P := differentiable_xiOffLineDivisor hfin
  have hPeven : ∀ z, P (-z) = P z := xiOffLineDivisor_neg hfin
  have hPconj : ∀ z, (starRingEnd ℂ) (P ((starRingEnd ℂ) z)) = P z :=
    listDivisor_quadrantListOf_conj _
  set B := ((xiOffLineList hfin).map fun β => 1 + 1 / ‖β‖ ^ 2).prod
  have hB0 : 0 ≤ B := List.prod_nonneg fun a ha => by
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha
    positivity
  have hPb : ∀ z, ‖P z‖ ≤ B * (1 + ‖z‖) ^ N := fun z => norm_listDivisor_le _ z
  by_cases hG0 : ∀ z, P z * H z = 0
  · refine ⟨0, by simp, fun z => ?_⟩
    rw [Polynomial.map_zero, Polynomial.eval_zero, mul_zero, mul_comm]
    exact hG0 z
  push Not at hG0
  obtain ⟨E, hEd, hE⟩ := GaloisForLFunctions.HTGeometry.exists_entire_quotient
    (f := fun w => P w * H w) (g := XiC) (hPd.mul hHd) XiC_differentiable
    ⟨0, XiC_ne_zero_of_norm_le_one (by simp)⟩ (analyticOrderAt_XiC_le_mul hfin hHd hkeep)
  obtain ⟨KX, hKX, hX⟩ := exists_norm_XiC_le_exp
  have hGenv : ∀ z, ‖P z * H z‖ ≤
      (B * C) * Real.exp ((N + KX) * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
    intro z
    have h1 := norm_sourceTransform_le hCv z
    have h2 : thetaSourceLaplace z.im ≤ Real.exp (KX * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
      rw [← norm_XiC_I_mul]
      refine (hX _).trans (Real.exp_le_exp.mpr ?_)
      have hn : ‖I * (z.im : ℂ)‖ ≤ ‖z‖ := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
        exact Complex.abs_im_le_norm z
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_left (shape_mono (norm_nonneg _) hn) hKX
    have h3 := one_add_norm_pow_le_exp_shape N z
    rw [norm_mul]
    calc ‖P z‖ * ‖H z‖ ≤ (B * (1 + ‖z‖) ^ N) * (C * thetaSourceLaplace z.im) :=
          mul_le_mul (hPb z) h1 (norm_nonneg _) (by positivity)
      _ ≤ (B * Real.exp (N * ((1 + ‖z‖) * Real.log (2 + ‖z‖)))) *
            (C * Real.exp (KX * (1 + ‖z‖) * Real.log (2 + ‖z‖))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h3 hB0) (mul_le_mul_of_nonneg_left h2 hC0)
            (mul_nonneg hC0 (thetaSourceLaplace_pos _).le) (mul_nonneg hB0 (Real.exp_pos _).le)
      _ = _ := by
          rw [show (N + KX) * (1 + ‖z‖) * Real.log (2 + ‖z‖) =
            N * ((1 + ‖z‖) * Real.log (2 + ‖z‖)) + KX * (1 + ‖z‖) * Real.log (2 + ‖z‖) by ring,
            Real.exp_add]
          ring
  obtain ⟨K, hK, henv⟩ := exists_quotient_envelope_of_bound (hPd.mul hHd) (mul_nonneg hB0 hC0)
    hGenv hE hEd hG0
  have him : ∀ y : ℝ, ‖E (y * I)‖ ≤ (C * B) * (1 + |y|) ^ N := by
    intro y
    have hL := thetaSourceLaplace_pos y
    have hXI : ‖XiC ((y : ℂ) * I)‖ = thetaSourceLaplace y := by
      rw [mul_comm]; exact norm_XiC_I_mul y
    have h1 := norm_sourceTransform_le hCv ((y : ℂ) * I)
    have hyI : ((y : ℂ) * I).im = y := by simp
    have hn : ‖(y : ℂ) * I‖ = |y| := by simp
    rw [hyI] at h1
    have h2 : ‖E (y * I)‖ * thetaSourceLaplace y ≤
        (C * B) * (1 + |y|) ^ N * thetaSourceLaplace y := by
      rw [← hXI, ← norm_mul, ← hE, norm_mul]
      calc ‖P (y * I)‖ * ‖H (y * I)‖ ≤ (B * (1 + |y|) ^ N) * (C * thetaSourceLaplace y) := by
            refine mul_le_mul ?_ h1 (norm_nonneg _) (by positivity)
            rw [← hn]; exact hPb _
        _ = _ := by rw [hXI]; ring
    exact le_of_mul_le_mul_right h2 hL
  have hl := fun α (hα : α ∈ hfin.toFinset.toList) => mem_xiOffLineList_toList hfin hα
  have hband : ∀ z : ℂ, 5 / 2 ≤ |z.im| → ‖E z‖ ≤ (3 * C * B) * (1 + ‖z‖) ^ N *
      Real.exp (|z.re| / 2 * Real.arctan (|z.re| / (1 / 2 + |z.im|))) := by
    intro z hz
    have hPz : P z ≠ 0 := listDivisor_quadrantListOf_ne_zero hl hz
    have hw : H z = (E z / P z) * XiC z := by
      have := hE z
      field_simp
      linear_combination this
    have h1 := norm_le_of_band_of_eq_mul hCv hz hw
    have hEz : E z = P z * (E z / P z) := by field_simp
    rw [hEz, norm_mul]
    calc ‖P z‖ * ‖E z / P z‖ ≤ (B * (1 + ‖z‖) ^ N) *
          (3 * C * Real.exp (|z.re| / 2 * Real.arctan (|z.re| / (1 / 2 + |z.im|)))) :=
          mul_le_mul (hPb z) h1 (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hrays := rays_of_band_bound hEd.continuous (C := 3 * C * B) (by positivity) N hband
  have htay := GaloisForLFunctions.HTGeometry.eq_taylor_of_imag_of_rays hEd N hK henv him hrays
  set c : ℕ → ℂ := fun i => GaloisForLFunctions.HTGeometry.dslopeIter E i 0 with hcdef
  have hXne : ∀ z : ℂ, ‖z‖ ≤ 1 → XiC z ≠ 0 := fun z hz => XiC_ne_zero_of_norm_le_one hz
  have hdisc_even : ∀ z : ℂ, ‖z‖ ≤ 1 → E (-z) = E z := by
    intro z hz
    have h1 := hE (-z)
    have h2 := hE z
    simp only [hPeven, hHeven, XiC_even] at h1
    exact mul_right_cancel₀ (hXne z hz) (h1.symm.trans h2)
  have hdisc_real : ∀ z : ℂ, ‖z‖ ≤ 1 → (starRingEnd ℂ) (E ((starRingEnd ℂ) z)) = E z := by
    intro z hz
    have h1 := congrArg (starRingEnd ℂ) (hE ((starRingEnd ℂ) z))
    simp only [map_mul, hPconj, hHconj, XiC_conj, Complex.conj_conj] at h1
    exact mul_right_cancel₀ (hXne z hz) (h1.symm.trans (hE z))
  have hodd : ∀ i < N + 1, c i * ((-1) ^ i - 1) = 0 := by
    refine coeff_eq_zero_of_sum_eq_zero_on_disc (c := fun i => c i * ((-1) ^ i - 1)) fun z hz => ?_
    have h := hdisc_even z hz
    rw [htay (-z), htay z] at h
    rw [← sub_eq_zero] at h
    rw [← h, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [neg_pow]; ring
  have hreal : ∀ i < N + 1, (starRingEnd ℂ) (c i) - c i = 0 := by
    refine coeff_eq_zero_of_sum_eq_zero_on_disc (c := fun i => (starRingEnd ℂ) (c i) - c i)
      fun z hz => ?_
    have h := hdisc_real z hz
    rw [htay ((starRingEnd ℂ) z), htay z] at h
    rw [← sub_eq_zero] at h
    rw [← h, map_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      simp only [map_mul, map_pow, Complex.conj_conj]; ring
  set e : Polynomial ℝ := ∑ j ∈ Finset.range (n + 1),
    Polynomial.C (c (2 * j)).re * Polynomial.X ^ j with hedef
  refine ⟨e, ?_, fun z => ?_⟩
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by
      have := Finset.mem_range.1 hj; omega)
  · have hcreal : ∀ j < n + 1, ((c (2 * j)).re : ℂ) = c (2 * j) := fun j hj =>
      Complex.conj_eq_iff_re.1 (sub_eq_zero.1 (hreal (2 * j) (by omega)))
    have hcodd : ∀ j < n, c (2 * j + 1) = 0 := fun j hj => by
      have h := hodd (2 * j + 1) (by omega)
      rw [pow_succ, pow_mul, neg_one_sq, one_pow] at h
      have : c (2 * j + 1) * (-2) = 0 := by linear_combination h
      simpa using this
    have hzero : ∑ j ∈ Finset.range n, c (2 * j + 1) * z ^ (2 * j + 1) = 0 :=
      Finset.sum_eq_zero fun j hj => by rw [hcodd j (Finset.mem_range.1 hj), zero_mul]
    have hval : (e.map (algebraMap ℝ ℂ)).eval (z ^ 2) = E z := by
      rw [htay z, hNdef, sum_range_two_mul_add_one, hzero, add_zero, hedef, Polynomial.map_sum,
        Polynomial.eval_finsetSum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
        Complex.coe_algebraMap, hcreal j (Finset.mem_range.1 hj), ← pow_mul]
    rw [hval, mul_comm (H z), mul_comm (XiC z)]
    exact hE z

end Classification

end

end RHTower
