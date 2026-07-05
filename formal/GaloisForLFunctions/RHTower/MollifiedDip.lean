/-
Doc 56 (the mollified dip scheme): the measure/counting layer, machine-checked.

Route B to (CR-density): every sliver zero of `F_N` forces a measurable dip of
the mollified sum `P = F_N·M_y` on the critical line (doc 56 §2, L²-only), and
3h-separated dips convert the dip-set measure into a zero COUNT. The kernel
(K-bdd) `volume {|P| ≤ r} ≤ C·r²·U` is the one open input; everything from the
per-zero J-average bound to the final count is proved here.

* `sublevel_half_of_average` — Chebyshev on an interval: a nonneg continuous f
  with J-average ≤ M satisfies f ≤ 2M on at least half of J.
* `dip_measure_lower` — the dip lemma's conclusion: the doc 56 §2 average bound
  2hB² + 4h²L² over J = [γ−h, γ+h] forces measure ≥ h of
  {f ≤ 2(B² + 2hL²)} inside J. The average bound itself (path Cauchy–Schwarz
  against P′) is the per-instance analytic input, hypothesis-typed per the
  house pattern; its discharge consumes the `SecondMoment.dpoly` L² bricks.
* `gapped_Icc_disjoint` / `separated_dips_count_le` — the counting bridge:
  3h-separated dip centers with per-dip measure ≥ h number at most
  (volume E)/h.
* `sliverCount_le_of_kernel` — assembly: (K-bdd) converts the count into
  card ≤ C·r²·U/h — doc 56 §4's endpoint with everything but the kernel
  machine-checked.
-/
import Mathlib

namespace RHTower

open MeasureTheory Set

/-- **Interval Chebyshev (doc 56 §2, last step).** A nonnegative continuous
function whose integral over `[a, b]` is at most `M·(b−a)` satisfies
`f ≤ 2M` on a subset of measure at least `(b−a)/2`. -/
theorem sublevel_half_of_average {a b M : ℝ} (hab : a < b) (hM : 0 < M)
    {f : ℝ → ℝ} (hf : Continuous f) (hnn : ∀ t, 0 ≤ f t)
    (havg : ∫ t in Icc a b, f t ≤ M * (b - a)) :
    ENNReal.ofReal ((b - a) / 2) ≤ volume {t ∈ Icc a b | f t ≤ 2 * M} := by
  set S : Set ℝ := {x | 2 * M ≤ f x} with hS
  have hSmeas : MeasurableSet S := by
    have : S = f ⁻¹' Ici (2 * M) := rfl
    rw [this]
    exact hf.measurable measurableSet_Ici
  -- Markov on the restricted measure
  have hmarkov : 2 * M * (volume.restrict (Icc a b)).real S
      ≤ ∫ t in Icc a b, f t :=
    mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall hnn) (hf.integrableOn_Icc) (2 * M)
  have hreal : (volume.restrict (Icc a b)).real S = volume.real (S ∩ Icc a b) :=
    measureReal_restrict_apply hSmeas
  have hSreal : volume.real (S ∩ Icc a b) ≤ (b - a) / 2 := by
    rw [hreal] at hmarkov
    nlinarith [hmarkov, havg]
  have hSfin : volume (S ∩ Icc a b) ≠ ⊤ := by
    have hle : volume (S ∩ Icc a b) ≤ volume (Icc a b) :=
      measure_mono inter_subset_right
    rw [Real.volume_Icc] at hle
    exact (lt_of_le_of_lt hle ENNReal.ofReal_lt_top).ne
  have hSball : volume (S ∩ Icc a b) ≤ ENNReal.ofReal ((b - a) / 2) :=
    (ENNReal.le_ofReal_iff_toReal_le hSfin (by linarith)).mpr hSreal
  -- cover J by the sublevel set and S ∩ J
  have hcover : Icc a b ⊆ {t ∈ Icc a b | f t ≤ 2 * M} ∪ (S ∩ Icc a b) := by
    intro t ht
    rcases le_total (f t) (2 * M) with hle | hge
    · exact Or.inl ⟨ht, hle⟩
    · exact Or.inr ⟨hge, ht⟩
  have hJ : ENNReal.ofReal (b - a)
      ≤ volume {t ∈ Icc a b | f t ≤ 2 * M} + ENNReal.ofReal ((b - a) / 2) := by
    calc ENNReal.ofReal (b - a) = volume (Icc a b) := (Real.volume_Icc).symm
      _ ≤ volume ({t ∈ Icc a b | f t ≤ 2 * M} ∪ (S ∩ Icc a b)) :=
          measure_mono hcover
      _ ≤ volume {t ∈ Icc a b | f t ≤ 2 * M} + volume (S ∩ Icc a b) :=
          measure_union_le _ _
      _ ≤ volume {t ∈ Icc a b | f t ≤ 2 * M} + ENNReal.ofReal ((b - a) / 2) := by
          gcongr
  have hsub : ENNReal.ofReal ((b - a) / 2)
      = ENNReal.ofReal (b - a) - ENNReal.ofReal ((b - a) / 2) := by
    rw [← ENNReal.ofReal_sub _ (by linarith : (0:ℝ) ≤ (b - a) / 2)]
    ring_nf
  rw [hsub]
  exact tsub_le_iff_right.mpr hJ

/-- **The dip lemma, conclusion form (doc 56 §2).** If the `J`-integral of a
nonnegative continuous `f` over `J = [γ−h, γ+h]` is at most `2hB² + 4h²L²`
(the path-Cauchy–Schwarz output at a sliver zero at depth `≤ h`), then
`f ≤ 2(B² + 2hL²)` on measure at least `h` inside `J`. -/
theorem dip_measure_lower {γ h B2 L2 : ℝ} (hh : 0 < h)
    (hpos : 0 < B2 + 2 * h * L2)
    {f : ℝ → ℝ} (hf : Continuous f) (hnn : ∀ t, 0 ≤ f t)
    (havg : ∫ t in Icc (γ - h) (γ + h), f t ≤ 2 * h * B2 + 4 * h ^ 2 * L2) :
    ENNReal.ofReal h
      ≤ volume {t ∈ Icc (γ - h) (γ + h) | f t ≤ 2 * (B2 + 2 * h * L2)} := by
  have hab : γ - h < γ + h := by linarith
  have havg' : ∫ t in Icc (γ - h) (γ + h), f t
      ≤ (B2 + 2 * h * L2) * ((γ + h) - (γ - h)) := by
    calc ∫ t in Icc (γ - h) (γ + h), f t ≤ 2 * h * B2 + 4 * h ^ 2 * L2 := havg
      _ = (B2 + 2 * h * L2) * ((γ + h) - (γ - h)) := by ring
  have := sublevel_half_of_average hab hpos hf hnn havg'
  have hhalf : ((γ + h) - (γ - h)) / 2 = h := by ring
  rwa [hhalf] at this

/-- Two `h`-intervals whose centers are `≥ 3h` apart are disjoint. -/
theorem gapped_Icc_disjoint {x y h : ℝ} (hh : 0 < h) (hgap : 3 * h ≤ |x - y|) :
    Disjoint (Icc (x - h) (x + h)) (Icc (y - h) (y + h)) := by
  rw [Set.disjoint_left]
  rintro t ⟨h1, h2⟩ ⟨h3, h4⟩
  rcases le_total x y with hxy | hxy
  · rw [abs_of_nonpos (by linarith)] at hgap; linarith
  · rw [abs_of_nonneg (by linarith)] at hgap; linarith

/-- **The counting bridge (doc 56 §4).** If `3h`-separated centers each
contribute measure `≥ h` of `E` inside their `h`-interval, the number of
centers is bounded by `(volume E)/h`, in the form
`card · h ≤ volume E`. -/
theorem separated_dips_count_le {E : Set ℝ} (hE : MeasurableSet E) {h : ℝ}
    (hh : 0 < h) (S : Finset ℝ)
    (hsep : (↑S : Set ℝ).Pairwise fun x y => 3 * h ≤ |x - y|)
    (hdip : ∀ γ ∈ S, ENNReal.ofReal h ≤ volume (E ∩ Icc (γ - h) (γ + h))) :
    (S.card : ENNReal) * ENNReal.ofReal h ≤ volume E := by
  have hdisj : (↑S : Set ℝ).PairwiseDisjoint
      (fun γ => E ∩ Icc (γ - h) (γ + h)) := by
    intro x hx y hy hxy
    exact ((gapped_Icc_disjoint hh (hsep hx hy hxy)).mono
      inter_subset_right inter_subset_right)
  have hmeas : ∀ γ ∈ S, MeasurableSet (E ∩ Icc (γ - h) (γ + h)) :=
    fun γ _ => hE.inter measurableSet_Icc
  calc (S.card : ENNReal) * ENNReal.ofReal h
      = ∑ _γ ∈ S, ENNReal.ofReal h := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ γ ∈ S, volume (E ∩ Icc (γ - h) (γ + h)) :=
        Finset.sum_le_sum hdip
    _ = volume (⋃ γ ∈ S, E ∩ Icc (γ - h) (γ + h)) :=
        (measure_biUnion_finset hdisj hmeas).symm
    _ ≤ volume E := by
        apply measure_mono
        simp only [Set.iUnion_subset_iff]
        exact fun γ _ => inter_subset_left

/-- **Assembly: the kernel prices the sliver count (doc 56 §§4–5).** With the
(K-bdd) kernel `volume E ≤ C·r²·U` for the dip set `E`, any `3h`-separated
family of dip centers satisfies `card·h ≤ C·r²·U` — the (CR-density) count in
the form the `creation_rate` consumer takes. -/
theorem sliverCount_le_of_kernel {E : Set ℝ} (hE : MeasurableSet E)
    {h C r U : ℝ} (hh : 0 < h) (hCU : 0 ≤ C * r ^ 2 * U) (S : Finset ℝ)
    (hsep : (↑S : Set ℝ).Pairwise fun x y => 3 * h ≤ |x - y|)
    (hdip : ∀ γ ∈ S, ENNReal.ofReal h ≤ volume (E ∩ Icc (γ - h) (γ + h)))
    (hker : volume E ≤ ENNReal.ofReal (C * r ^ 2 * U)) :
    (S.card : ℝ) * h ≤ C * r ^ 2 * U := by
  have h1 := (separated_dips_count_le hE hh S hsep hdip).trans hker
  have h2 : ENNReal.ofReal ((S.card : ℝ) * h)
      = (S.card : ENNReal) * ENNReal.ofReal h := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  have h3 : ENNReal.ofReal ((S.card : ℝ) * h)
      ≤ ENNReal.ofReal (C * r ^ 2 * U) := by rw [h2]; exact h1
  have h4 := ENNReal.toReal_le_of_le_ofReal hCU h3
  rwa [ENNReal.toReal_ofReal (by positivity)] at h4

end RHTower

namespace RHTower

open MeasureTheory Set

/-- **Average-to-count endpoint (doc 56 §§2,4).** If every separated center has
the path-average bound from the dip lemma, and the resulting sublevel set has
the kernel measure bound, then the sliver count follows. This removes the
intermediate per-center `hdip` package from downstream consumers. -/
theorem sliverCount_le_of_average_kernel
    {h B2 L2 C r U : ℝ} (hh : 0 < h) (hpos : 0 < B2 + 2 * h * L2)
    (hCU : 0 ≤ C * r ^ 2 * U)
    {f : ℝ → ℝ} (hf : Continuous f) (hnn : ∀ t, 0 ≤ f t) (S : Finset ℝ)
    (hsep : (↑S : Set ℝ).Pairwise fun x y => 3 * h ≤ |x - y|)
    (havg : ∀ γ ∈ S,
      ∫ t in Icc (γ - h) (γ + h), f t ≤ 2 * h * B2 + 4 * h ^ 2 * L2)
    (hker : volume {t | f t ≤ 2 * (B2 + 2 * h * L2)} ≤ ENNReal.ofReal (C * r ^ 2 * U)) :
    (S.card : ℝ) * h ≤ C * r ^ 2 * U := by
  let E : Set ℝ := {t | f t ≤ 2 * (B2 + 2 * h * L2)}
  have hE : MeasurableSet E := by
    change MeasurableSet (f ⁻¹' Iic (2 * (B2 + 2 * h * L2)))
    exact hf.measurable measurableSet_Iic
  have hdip : ∀ γ ∈ S, ENNReal.ofReal h ≤ volume (E ∩ Icc (γ - h) (γ + h)) := by
    intro γ hγ
    have hmeasure := dip_measure_lower hh hpos hf hnn (havg γ hγ)
    have hset : {t ∈ Icc (γ - h) (γ + h) | f t ≤ 2 * (B2 + 2 * h * L2)}
        = E ∩ Icc (γ - h) (γ + h) := by
      ext t
      constructor
      · intro ht
        exact ⟨ht.2, ht.1⟩
      · intro ht
        exact ⟨ht.2, ht.1⟩
    rwa [hset] at hmeasure
  exact sliverCount_le_of_kernel hE hh hCU S hsep hdip hker

/-- **Integer creation-budget form.** The mollified dip estimate gives the
natural-number count used by `MidCentral` once the real measure budget lies
strictly below the next integer multiple of the per-dip width. -/
theorem sliverCount_card_le_of_average_kernel
    {h B2 L2 C r U : ℝ} (hh : 0 < h) (hpos : 0 < B2 + 2 * h * L2)
    (hCU : 0 ≤ C * r ^ 2 * U)
    {f : ℝ → ℝ} (hf : Continuous f) (hnn : ∀ t, 0 ≤ f t) (S : Finset ℝ)
    (hsep : (↑S : Set ℝ).Pairwise fun x y => 3 * h ≤ |x - y|)
    (havg : ∀ γ ∈ S,
      ∫ t in Icc (γ - h) (γ + h), f t ≤ 2 * h * B2 + 4 * h ^ 2 * L2)
    (hker : volume {t | f t ≤ 2 * (B2 + 2 * h * L2)}
      ≤ ENNReal.ofReal (C * r ^ 2 * U))
    {K : ℕ} (hK : C * r ^ 2 * U < (K + 1 : ℝ) * h) :
    S.card ≤ K := by
  have hcount :=
    sliverCount_le_of_average_kernel hh hpos hCU hf hnn S hsep havg hker
  have hcard_lt_real : (S.card : ℝ) < (K + 1 : ℝ) := by
    have hlt : (S.card : ℝ) * h < (K + 1 : ℝ) * h :=
      lt_of_le_of_lt hcount hK
    nlinarith
  have hcard_lt_nat : S.card < K + 1 := by
    exact_mod_cast hcard_lt_real
  exact Nat.lt_succ_iff.mp hcard_lt_nat

end RHTower
