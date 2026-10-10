import GaloisForLFunctions.RHTower.XiGaussianHeatZeroFreeHalfPlane

/-!
# The negative index of the vertical heat Gram form

Weights are finitely supported complex measures on `ℝ`, i.e. elements of the group algebra
`ℂ[ℝ]` (`HeatWeights`).  The vertical heat Gram form at heat time `a > 0` is
`Q_a(c, d) = Σ_{s,t} c(s) \overline{d(t)} ν(a + i(s − t))`.  With the amplitude
`A_c(w) = Σ_s c(s) e^{-isw}`, an algebra homomorphism `ℂ[ℝ] → ℂ`,

`Q_a(c, d) = Σ_q e^{-a w_q} A_c(w_q) \overline{A_d(\overline{w_q})}`   (`heatGram_eq_tsum`).

A real frequency contributes `e^{-aλ}|A_c(λ)|² ≥ 0`; an off-line pair `w, w̄` contributes the
indefinite rank-two form `2 Re(e^{-aw} A_c(w) \overline{A_c(w̄)})`.

Let `U` be the set of squared spectral points `w = z_q²` with `Im w > 0`.  Since `z ↦ z²` identifies
`±z`, `U` is in bijection with the off-line zero quadruples `{ρ, 1 − ρ, ρ̄, 1 − ρ̄}`.

**Theorem** (`heatGram_negativeIndex_eq_card`).  If `U` is finite, then for every `a > 0` the
negative index of `Q_a` is `#U`: every subspace on which `Q_a` is negative definite has dimension at
most `#U`, and some subspace of dimension `#U` is negative definite.

The upper bound is the kernel of `c ↦ (A_c(w))_{w ∈ U}`.  For the lower bound, the amplitude of
`(1 + t δ_L) ∏_{v ≠ u} (1 − e^{iℓv} δ_ℓ)(1 − e^{iℓv̄} δ_ℓ)` vanishes at every off-line frequency
other than `u, ū`, is bounded on the real frequencies independently of `L`, and its rank-two
contribution at `u` is `≤ 3‖κ‖ − ‖κ‖ e^{L Im u}`.

**Theorem** (`riemannHypothesis_iff_heatGram_nonneg`).  For each `a > 0`, RH holds iff `Q_a` is
positive semidefinite.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-! ## Weights, amplitudes and the Gram form -/

/-- Finitely supported complex weights on `ℝ` with convolution. -/
abbrev HeatWeights := AddMonoidAlgebra ℂ ℝ

/-- The character `s ↦ e^{-isw}` of `ℝ`. -/
def heatCharacter (w : ℂ) : Multiplicative ℝ →* ℂ where
  toFun s := Complex.exp (-(I * ((Multiplicative.toAdd s : ℝ) : ℂ)) * w)
  map_one' := by simp
  map_mul' s t := by
    rw [← Complex.exp_add]
    congr 1
    simp only [toAdd_mul, ofReal_add]
    ring

/-- The amplitude `A_c(w) = Σ_s c(s) e^{-isw}`. -/
def heatAmp (w : ℂ) : HeatWeights →ₐ[ℂ] ℂ := AddMonoidAlgebra.lift ℂ ℂ ℝ (heatCharacter w)

theorem heatAmp_apply (w : ℂ) (c : HeatWeights) :
    heatAmp w c = c.coeff.sum fun s x => x * Complex.exp (-(I * (s : ℂ)) * w) := by
  rw [heatAmp, AddMonoidAlgebra.lift_apply]
  rfl

theorem heatAmp_single (w : ℂ) (s : ℝ) (x : ℂ) :
    heatAmp w (AddMonoidAlgebra.single s x) = x * Complex.exp (-(I * (s : ℂ)) * w) := by
  rw [heatAmp, AddMonoidAlgebra.lift_single]
  rfl

theorem heatAmp_smul (w x : ℂ) (c : HeatWeights) : heatAmp w (x • c) = x * heatAmp w c := by
  simp

theorem conj_heatAmp_conj (w : ℂ) (c : HeatWeights) :
    (starRingEnd ℂ) (heatAmp ((starRingEnd ℂ) w) c) =
      c.coeff.sum fun t y => (starRingEnd ℂ) y * Complex.exp (I * (t : ℂ) * w) := by
  rw [heatAmp_apply, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_mul, ← Complex.exp_conj]
  congr 2
  simp [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]

/-- The vertical heat Gram form `Q_a(c, d) = Σ_{s,t} c(s) \overline{d(t)} ν(a + i(s − t))`. -/
def heatGram (a : ℝ) (c d : HeatWeights) : ℂ :=
  c.coeff.sum fun s x => d.coeff.sum fun t y =>
    x * (starRingEnd ℂ) y * xiGaussianHeatTraceC ((a : ℂ) + ((s - t : ℝ) : ℂ) * I)

/-- The contribution `e^{-aw} A_c(w) \overline{A_d(w̄)}` of a frequency `w`. -/
def heatGramTermAt (a : ℝ) (c d : HeatWeights) (w : ℂ) : ℂ :=
  Complex.exp (-(a : ℂ) * w) * heatAmp w c * (starRingEnd ℂ) (heatAmp ((starRingEnd ℂ) w) d)

theorem heatGramTermAt_eq_sum (a : ℝ) (c d : HeatWeights) (w : ℂ) :
    heatGramTermAt a c d w = c.coeff.sum fun s x => d.coeff.sum fun t y =>
      x * (starRingEnd ℂ) y * Complex.exp (-((a : ℂ) + ((s - t : ℝ) : ℂ) * I) * w) := by
  rw [heatGramTermAt, conj_heatAmp_conj, heatAmp_apply, mul_assoc]
  simp only [Finsupp.sum]
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hexp : Complex.exp (-((a : ℂ) + ((s - t : ℝ) : ℂ) * I) * w) =
      Complex.exp (-(a : ℂ) * w) * Complex.exp (-(I * (s : ℂ)) * w) *
        Complex.exp (I * (t : ℂ) * w) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hexp]
  ring

theorem summable_exp_neg_mul_xiHeatFrequency {τ : ℂ} (hτ : 0 < τ.re) :
    Summable fun q : XiZeroCopy => Complex.exp (-τ * xiHeatFrequency q) :=
  (summable_norm_xiGaussianHeatTermC hτ).of_norm

theorem summable_heatGramTermAt {a : ℝ} (ha : 0 < a) (c d : HeatWeights) :
    Summable fun q : XiZeroCopy => heatGramTermAt a c d (xiHeatFrequency q) := by
  have hre : ∀ β : ℝ, 0 < ((a : ℂ) + (β : ℂ) * I).re := fun β => by simpa using ha
  simp only [heatGramTermAt_eq_sum, Finsupp.sum]
  exact summable_sum fun s _ => summable_sum fun t _ =>
    (summable_exp_neg_mul_xiHeatFrequency (hre _)).mul_left _

/-- **Expansion of the Gram form over the zeros.** -/
theorem heatGram_eq_tsum {a : ℝ} (ha : 0 < a) (c d : HeatWeights) :
    heatGram a c d = ∑' q : XiZeroCopy, heatGramTermAt a c d (xiHeatFrequency q) := by
  have hre : ∀ β : ℝ, 0 < ((a : ℂ) + (β : ℂ) * I).re := fun β => by simpa using ha
  have hs : ∀ s t : ℝ, Summable fun q : XiZeroCopy => c.coeff s * (starRingEnd ℂ) (d.coeff t) *
      Complex.exp (-((a : ℂ) + ((s - t : ℝ) : ℂ) * I) * xiHeatFrequency q) := fun s t =>
    (summable_exp_neg_mul_xiHeatFrequency (hre _)).mul_left _
  simp only [heatGramTermAt_eq_sum, heatGram, Finsupp.sum]
  rw [Summable.tsum_finsetSum fun s _ => summable_sum fun t _ => hs s t]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Summable.tsum_finsetSum fun t _ => hs s t]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [tsum_mul_left, xiGaussianHeatTraceC]
  rfl

theorem heatGram_add_left (a : ℝ) (c c' d : HeatWeights) :
    heatGram a (c + c') d = heatGram a c d + heatGram a c' d := by
  unfold heatGram
  rw [AddMonoidAlgebra.coeff_add, Finsupp.sum_add_index']
  · intro s; simp
  · intro s x₁ x₂
    simp only [add_mul, Finsupp.sum_add]

theorem heatGram_add_right (a : ℝ) (c d d' : HeatWeights) :
    heatGram a c (d + d') = heatGram a c d + heatGram a c d' := by
  have h : ∀ (s : ℝ) (x : ℂ), ((d + d').coeff.sum fun t y =>
      x * (starRingEnd ℂ) y * xiGaussianHeatTraceC ((a : ℂ) + ((s - t : ℝ) : ℂ) * I)) =
      (d.coeff.sum fun t y =>
        x * (starRingEnd ℂ) y * xiGaussianHeatTraceC ((a : ℂ) + ((s - t : ℝ) : ℂ) * I)) +
      (d'.coeff.sum fun t y =>
        x * (starRingEnd ℂ) y * xiGaussianHeatTraceC ((a : ℂ) + ((s - t : ℝ) : ℂ) * I)) := by
    intro s x
    rw [AddMonoidAlgebra.coeff_add, Finsupp.sum_add_index']
    · intro t; simp
    · intro t y₁ y₂; rw [map_add]; ring
  unfold heatGram
  simp only [h, Finsupp.sum_add]

theorem heatGram_single_single (a s t : ℝ) (x y : ℂ) :
    heatGram a (AddMonoidAlgebra.single s x) (AddMonoidAlgebra.single t y) =
      x * (starRingEnd ℂ) y * xiGaussianHeatTraceC ((a : ℂ) + ((s - t : ℝ) : ℂ) * I) := by
  simp [heatGram, Finsupp.sum_single_index]

theorem heatGram_zero_left (a : ℝ) (d : HeatWeights) : heatGram a 0 d = 0 := by
  simp [heatGram]

/-! ## Positivity, the upper bound, and RH -/

/-- The off-line frequencies in the upper half-plane. -/
def xiUpperFrequencies : Set ℂ := {w | ∃ q : XiZeroCopy, xiHeatFrequency q = w ∧ 0 < w.im}

theorem heatGramTermAt_conj (a : ℝ) (c : HeatWeights) (w : ℂ) :
    heatGramTermAt a c c ((starRingEnd ℂ) w) = (starRingEnd ℂ) (heatGramTermAt a c c w) := by
  simp only [heatGramTermAt, map_mul, Complex.conj_conj, ← Complex.exp_conj, map_neg,
    Complex.conj_ofReal]
  ring

theorem re_heatGramTermAt_of_im_eq_zero (a : ℝ) (c : HeatWeights) {w : ℂ} (hw : w.im = 0) :
    (heatGramTermAt a c c w).re = Real.exp (-(a * w.re)) * ‖heatAmp w c‖ ^ 2 := by
  have hreal : (starRingEnd ℂ) w = w := Complex.conj_eq_iff_im.2 hw
  have hexp : Complex.exp (-(a : ℂ) * w) = ((Real.exp (-(a * w.re)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    apply Complex.ext <;> simp [hw]
  rw [heatGramTermAt, hreal, hexp, mul_assoc, Complex.mul_conj, ← Complex.ofReal_mul,
    Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- The Gram form is nonnegative on weights whose amplitude vanishes at the upper frequencies. -/
theorem heatGram_re_nonneg_of_amp_vanish {a : ℝ} (ha : 0 < a) (c : HeatWeights)
    (hc : ∀ w ∈ xiUpperFrequencies, heatAmp w c = 0) : 0 ≤ (heatGram a c c).re := by
  rw [heatGram_eq_tsum ha, Complex.re_tsum (summable_heatGramTermAt ha c c)]
  refine tsum_nonneg fun q => ?_
  set w := xiHeatFrequency q with hw
  rcases lt_trichotomy w.im 0 with him | him | him
  · have hc' : heatAmp ((starRingEnd ℂ) w) c = 0 := by
      refine hc _ ⟨xiZeroCopyLineConjEquiv q, by rw [xiHeatFrequency_lineConj], ?_⟩
      rw [Complex.conj_im]; linarith
    rw [heatGramTermAt, hc', map_zero, mul_zero, zero_re]
  · rw [re_heatGramTermAt_of_im_eq_zero a c him]
    positivity
  · rw [heatGramTermAt, hc w ⟨q, rfl, him⟩, mul_zero, zero_mul, zero_re]

/-- **Upper bound.**  A subspace on which the Gram form is negative definite has dimension at most
the number of upper off-line frequencies. -/
theorem finrank_le_of_heatGram_neg {a : ℝ} (ha : 0 < a) (hU : xiUpperFrequencies.Finite)
    (V : Submodule ℂ HeatWeights) (hV : ∀ c ∈ V, c ≠ 0 → (heatGram a c c).re < 0) :
    Module.finrank ℂ V ≤ hU.toFinset.card := by
  classical
  set L : HeatWeights →ₗ[ℂ] (hU.toFinset → ℂ) :=
    LinearMap.pi fun w => (heatAmp (w : ℂ)).toLinearMap with hL
  have hinj : Function.Injective (L.domRestrict V) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    by_contra hne
    have hc0 : (c : HeatWeights) ≠ 0 := fun h => hne (Subtype.ext h)
    have hvan : ∀ w ∈ xiUpperFrequencies, heatAmp w (c : HeatWeights) = 0 := by
      intro w hw
      have := congrFun hc ⟨w, hU.mem_toFinset.2 hw⟩
      simpa [hL] using this
    have h1 := heatGram_re_nonneg_of_amp_vanish ha (c : HeatWeights) hvan
    have h2 := hV c c.2 hc0
    linarith
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h

/-- **RH is index zero.**  For `a > 0`, RH holds iff the vertical heat Gram form `Q_a` is positive
semidefinite. -/
theorem riemannHypothesis_iff_heatGram_nonneg {a : ℝ} (ha : 0 < a) :
    RiemannHypothesis ↔ ∀ c : HeatWeights, 0 ≤ (heatGram a c c).re := by
  constructor
  · intro hRH c
    refine heatGram_re_nonneg_of_amp_vanish ha c fun w hw => ?_
    exfalso
    obtain ⟨q, rfl, him⟩ := hw
    have h0 : (xiSpectralPoint q).im = 0 :=
      (riemannHypothesis_iff_forall_xiSpectralPoint_im_eq_zero).1 hRH q
    rw [xiHeatFrequency_im, h0, mul_zero] at him
    exact lt_irrefl 0 him
  · intro h
    rw [riemannHypothesis_iff_xiGaussianHeatTraceC_bounded_on_vertical_line ha]
    have hν0 : 0 ≤ (xiGaussianHeatTraceC (a : ℂ)).re := by
      have := h (AddMonoidAlgebra.single 0 1)
      simpa [heatGram_single_single] using this
    refine ⟨(xiGaussianHeatTraceC (a : ℂ)).re, fun β => ?_⟩
    set u := xiGaussianHeatTraceC ((a : ℂ) + (β : ℂ) * I) with hu
    by_cases hu0 : u = 0
    · rw [hu0, norm_zero]
      exact hν0
    · set t : ℂ := -((starRingEnd ℂ) u / (‖u‖ : ℂ)) with ht
      have hn : (‖u‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hu0)
      have hQ := h (AddMonoidAlgebra.single 0 1 + AddMonoidAlgebra.single β t)
      rw [heatGram_add_left, heatGram_add_right, heatGram_add_right, heatGram_single_single,
        heatGram_single_single, heatGram_single_single, heatGram_single_single] at hQ
      simp only [sub_self, zero_sub, sub_zero, ofReal_zero, zero_mul, add_zero, map_one, one_mul,
        mul_one] at hQ
      have hconj : xiGaussianHeatTraceC ((a : ℂ) + ((-β : ℝ) : ℂ) * I) = (starRingEnd ℂ) u := by
        rw [hu, ← xiGaussianHeatTraceC_conj]
        congr 1
        apply Complex.ext <;> simp
      rw [hconj, ← hu] at hQ
      have ht1 : t * u = -(‖u‖ : ℂ) := by
        rw [ht, neg_mul, div_mul_eq_mul_div, mul_comm ((starRingEnd ℂ) u), Complex.mul_conj,
          Complex.normSq_eq_norm_sq]
        push_cast
        field_simp
      have ht2 : (starRingEnd ℂ) t * (starRingEnd ℂ) u = -(‖u‖ : ℂ) := by
        rw [← map_mul, ht1, map_neg, Complex.conj_ofReal]
      have htn : ‖t‖ = 1 := by
        rw [ht, norm_neg, norm_div, Complex.norm_conj, Complex.norm_real,
          Real.norm_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.2 hu0)]
      have ht3 : t * (starRingEnd ℂ) t = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, htn]
        norm_num
      have hQ' : xiGaussianHeatTraceC (a : ℂ) + (starRingEnd ℂ) t * (starRingEnd ℂ) u +
          (t * u + t * (starRingEnd ℂ) t * xiGaussianHeatTraceC (a : ℂ)) =
          2 * xiGaussianHeatTraceC (a : ℂ) - 2 * (‖u‖ : ℂ) := by
        linear_combination ht2 + ht1 + xiGaussianHeatTraceC (a : ℂ) * ht3
      rw [hQ'] at hQ
      simp only [sub_re, mul_re, ofReal_re, ofReal_im, re_ofNat, im_ofNat, zero_mul, sub_zero,
        mul_zero] at hQ
      linarith

/-! ## Killer and main factors -/

/-- The factor `1 − e^{iℓv} δ_ℓ`; its amplitude `1 − e^{iℓ(v − w)}` vanishes at `w = v`. -/
def heatKillerFactor (ℓ : ℝ) (v : ℂ) : HeatWeights :=
  1 - AddMonoidAlgebra.single ℓ (Complex.exp (I * (ℓ : ℂ) * v))

theorem heatAmp_killerFactor (ℓ : ℝ) (v w : ℂ) :
    heatAmp w (heatKillerFactor ℓ v) = 1 - Complex.exp (I * (ℓ : ℂ) * (v - w)) := by
  rw [heatKillerFactor, map_sub, map_one, heatAmp_single, ← Complex.exp_add]
  congr 2
  ring

theorem heatAmp_killerFactor_self (ℓ : ℝ) (v : ℂ) : heatAmp v (heatKillerFactor ℓ v) = 0 := by
  rw [heatAmp_killerFactor, sub_self, mul_zero, Complex.exp_zero, sub_self]

theorem heatAmp_killerFactor_ne_zero {ℓ : ℝ} {v w : ℂ} (hℓ : 0 < ℓ) (hvw : v ≠ w)
    (hsmall : ℓ * ‖v - w‖ < 2 * Real.pi) : heatAmp w (heatKillerFactor ℓ v) ≠ 0 := by
  rw [heatAmp_killerFactor, sub_ne_zero, ne_comm, Ne, Complex.exp_eq_one_iff]
  rintro ⟨n, hn⟩
  have h1 : (ℓ : ℂ) * (v - w) = (((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) := by
    push_cast
    linear_combination (-I) * hn + ((ℓ : ℂ) * (v - w) - n * (2 * Real.pi)) * Complex.I_sq
  have h2 : |(n : ℝ)| * (2 * Real.pi) < 1 * (2 * Real.pi) := by
    have := congrArg norm h1
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hℓ.le, Complex.norm_real,
      Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at this
    linarith
  have hn0 : n = 0 := by
    have h3 : |(n : ℝ)| < 1 := lt_of_mul_lt_mul_right h2 (by positivity)
    have h4 : |n| < 1 := by exact_mod_cast h3
    exact Int.abs_lt_one_iff.1 h4
  rw [hn0] at h1
  have h5 : (ℓ : ℂ) * (v - w) = 0 := by simpa using h1
  rcases mul_eq_zero.1 h5 with h | h
  · exact hℓ.ne' (by exact_mod_cast h)
  · exact hvw (sub_eq_zero.1 h)

/-- The killer `∏_{v ∈ F, v ≠ u} (1 − e^{iℓv} δ_ℓ)(1 − e^{iℓv̄} δ_ℓ)`. -/
def heatKiller (ℓ : ℝ) (F : Finset ℂ) (u : ℂ) : HeatWeights :=
  ∏ v ∈ F.erase u, (heatKillerFactor ℓ v * heatKillerFactor ℓ ((starRingEnd ℂ) v))

theorem heatAmp_killer_eq_zero {ℓ : ℝ} {F : Finset ℂ} {u v : ℂ} (hv : v ∈ F) (hvu : v ≠ u) :
    heatAmp v (heatKiller ℓ F u) = 0 ∧ heatAmp ((starRingEnd ℂ) v) (heatKiller ℓ F u) = 0 := by
  have hmem : v ∈ F.erase u := Finset.mem_erase.2 ⟨hvu, hv⟩
  constructor
  · rw [heatKiller, map_prod]
    exact Finset.prod_eq_zero hmem (by rw [map_mul, heatAmp_killerFactor_self, zero_mul])
  · rw [heatKiller, map_prod]
    exact Finset.prod_eq_zero hmem (by rw [map_mul, heatAmp_killerFactor_self, mul_zero])

theorem heatAmp_killer_ne_zero {ℓ : ℝ} {F : Finset ℂ} {u w : ℂ} (hℓ : 0 < ℓ)
    (hne : ∀ v ∈ F.erase u, v ≠ w ∧ (starRingEnd ℂ) v ≠ w)
    (hsmall : ∀ v ∈ F.erase u,
      ℓ * ‖v - w‖ < 2 * Real.pi ∧ ℓ * ‖(starRingEnd ℂ) v - w‖ < 2 * Real.pi) :
    heatAmp w (heatKiller ℓ F u) ≠ 0 := by
  rw [heatKiller, map_prod]
  refine Finset.prod_ne_zero_iff.2 fun v hv => ?_
  rw [map_mul]
  exact mul_ne_zero (heatAmp_killerFactor_ne_zero hℓ (hne v hv).1 (hsmall v hv).1)
    (heatAmp_killerFactor_ne_zero hℓ (hne v hv).2 (hsmall v hv).2)

/-- The total mass `Σ_s |c(s)|`. -/
def heatMass (c : HeatWeights) : ℝ := c.coeff.sum fun _ x => ‖x‖

theorem norm_heatAmp_le_heatMass {w : ℂ} (hw : w.im = 0) (c : HeatWeights) :
    ‖heatAmp w c‖ ≤ heatMass c := by
  rw [heatAmp_apply, heatMass, Finsupp.sum, Finsupp.sum]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun s _ => ?_))
  rw [norm_mul, Complex.norm_exp]
  simp [hw]

/-- The main factor `1 + t δ_L`. -/
def heatMainFactor (L : ℝ) (t : ℂ) : HeatWeights := 1 + AddMonoidAlgebra.single L t

theorem heatAmp_mainFactor (L : ℝ) (t w : ℂ) :
    heatAmp w (heatMainFactor L t) = 1 + t * Complex.exp (-(I * (L : ℂ)) * w) := by
  rw [heatMainFactor, map_add, map_one, heatAmp_single]

theorem norm_heatAmp_mainFactor_le {L : ℝ} {t w : ℂ} (ht : ‖t‖ = 1) (hw : w.im = 0) :
    ‖heatAmp w (heatMainFactor L t)‖ ≤ 2 := by
  rw [heatAmp_mainFactor]
  refine (norm_add_le _ _).trans ?_
  rw [norm_one, norm_mul, ht, Complex.norm_exp]
  have : (-(I * (L : ℂ)) * w).re = 0 := by simp [hw]
  rw [this, Real.exp_zero]
  norm_num

/-- **One off-line pair.**  For `κ ≠ 0` and `Im u > 0`, the rank-two contribution
`Re(κ A(u) \overline{A(ū)})` of `A = 1 + t δ_L` can be made `≤ -M` with `|t| = 1`. -/
theorem exists_mainFactor_re_le {κ u : ℂ} (hκ : κ ≠ 0) (hu : 0 < u.im) (M : ℝ) :
    ∃ L : ℝ, ∃ t : ℂ, ‖t‖ = 1 ∧
      (κ * heatAmp u (heatMainFactor L t) *
        (starRingEnd ℂ) (heatAmp ((starRingEnd ℂ) u) (heatMainFactor L t))).re ≤ -M := by
  have hκn : 0 < ‖κ‖ := norm_pos_iff.2 hκ
  set M' := (3 * ‖κ‖ + |M| + 1) / ‖κ‖ with hM'
  have hM'1 : 1 < M' := by
    rw [hM', lt_div_iff₀ hκn]
    linarith [abs_nonneg M]
  set L := Real.log M' / u.im with hL
  have hLnn : 0 ≤ L := div_nonneg (Real.log_nonneg hM'1.le) hu.le
  have hLexp : Real.exp (L * u.im) = M' := by
    rw [hL, div_mul_cancel₀ _ hu.ne', Real.exp_log (by linarith)]
  set E := Complex.exp (-(I * (L : ℂ)) * u) with hE
  set E' := Complex.exp (I * (L : ℂ) * u) with hE'
  have hEnorm : ‖E‖ = M' := by
    rw [hE, Complex.norm_exp, ← hLexp]
    congr 1
    simp
  have hE'norm : ‖E'‖ ≤ 1 := by
    rw [hE', Complex.norm_exp]
    have : (I * (L : ℂ) * u).re = -(L * u.im) := by simp
    rw [this, Real.exp_le_one_iff]
    nlinarith
  have hEE' : E * E' = 1 := by
    rw [hE, hE', ← Complex.exp_add]
    rw [show -(I * (L : ℂ)) * u + I * (L : ℂ) * u = 0 by ring, Complex.exp_zero]
  have hκE : κ * E ≠ 0 := mul_ne_zero hκ (Complex.exp_ne_zero _)
  set t : ℂ := -((starRingEnd ℂ) (κ * E) / (‖κ * E‖ : ℂ)) with ht
  have hn : (‖κ * E‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hκE)
  have htn : ‖t‖ = 1 := by
    rw [ht, norm_neg, norm_div, Complex.norm_conj, Complex.norm_real,
      Real.norm_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.2 hκE)]
  have htE : κ * t * E = -(‖κ * E‖ : ℂ) := by
    rw [ht, show κ * -((starRingEnd ℂ) (κ * E) / (‖κ * E‖ : ℂ)) * E =
      -((κ * E) * (starRingEnd ℂ) (κ * E) / (‖κ * E‖ : ℂ)) by ring, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast
    field_simp
  have httc : t * (starRingEnd ℂ) t = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, htn]
    norm_num
  refine ⟨L, t, htn, ?_⟩
  have hamp2 : (starRingEnd ℂ) (heatAmp ((starRingEnd ℂ) u) (heatMainFactor L t)) =
      1 + (starRingEnd ℂ) t * E' := by
    rw [heatAmp_mainFactor, map_add, map_one, map_mul, ← Complex.exp_conj, hE']
    congr 3
    simp [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
  rw [heatAmp_mainFactor, ← hE, hamp2]
  have hexpand : κ * (1 + t * E) * (1 + (starRingEnd ℂ) t * E') =
      2 * κ + κ * t * E + κ * (starRingEnd ℂ) t * E' := by
    linear_combination κ * E * E' * httc + κ * hEE'
  rw [hexpand, htE]
  have h1 : (2 * κ).re ≤ 2 * ‖κ‖ := by
    rw [show (2 * κ).re = 2 * κ.re by simp]
    linarith [Complex.re_le_norm κ]
  have h2 : (κ * (starRingEnd ℂ) t * E').re ≤ ‖κ‖ := by
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_conj, htn, mul_one]
    exact mul_le_of_le_one_right (norm_nonneg _) hE'norm
  have h3 : (-(‖κ * E‖ : ℂ)).re = -(‖κ‖ * M') := by
    rw [neg_re, ofReal_re, norm_mul, hEnorm]
  have h4 : ‖κ‖ * M' = 3 * ‖κ‖ + |M| + 1 := by
    rw [hM']
    field_simp
  rw [add_re, add_re, h3]
  linarith [le_abs_self M]

/-! ## The lower bound -/

theorem heatAmp_sum_smul {ι : Type*} [Fintype ι] (w : ℂ) (A : ι → HeatWeights) (x : ι → ℂ) :
    heatAmp w (∑ u, x u • A u) = ∑ u, x u * heatAmp w (A u) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun u _ => heatAmp_smul w (x u) (A u)

/-- **Localization.**  If every weight but `A v` vanishes at `w` and `w̄`, the frequency `w` sees only
the `v`-component. -/
theorem heatGramTermAt_sum_eq_of_vanish {ι : Type*} [Fintype ι] (a : ℝ) (A : ι → HeatWeights)
    (x : ι → ℂ) (v : ι) (w : ℂ)
    (hvan : ∀ u, u ≠ v → heatAmp w (A u) = 0 ∧ heatAmp ((starRingEnd ℂ) w) (A u) = 0) :
    heatGramTermAt a (∑ u, x u • A u) (∑ u, x u • A u) w =
      ((‖x v‖ ^ 2 : ℝ) : ℂ) * heatGramTermAt a (A v) (A v) w := by
  have h1 : heatAmp w (∑ u, x u • A u) = x v * heatAmp w (A v) := by
    rw [heatAmp_sum_smul, Finset.sum_eq_single v]
    · intro u _ hu; rw [(hvan u hu).1, mul_zero]
    · intro h; exact absurd (Finset.mem_univ v) h
  have h2 : heatAmp ((starRingEnd ℂ) w) (∑ u, x u • A u) =
      x v * heatAmp ((starRingEnd ℂ) w) (A v) := by
    rw [heatAmp_sum_smul, Finset.sum_eq_single v]
    · intro u _ hu; rw [(hvan u hu).2, mul_zero]
    · intro h; exact absurd (Finset.mem_univ v) h
  have hx : x v * (starRingEnd ℂ) (x v) = ((‖x v‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [heatGramTermAt, heatGramTermAt, h1, h2, map_mul]
  linear_combination (Complex.exp (-(a : ℂ) * w) * heatAmp w (A v) *
    (starRingEnd ℂ) (heatAmp ((starRingEnd ℂ) w) (A v))) * hx

/-- **Real frequencies.**  At a real frequency the Gram term of `Σ x_u A_u` is at most
`#ι Σ_u |x_u|² D_u² e^{-aw}` when `|A_u(w)| ≤ D_u`. -/
theorem re_heatGramTermAt_sum_le_of_im_eq_zero {ι : Type*} [Fintype ι] (a : ℝ)
    (A : ι → HeatWeights) (x : ι → ℂ) {w : ℂ} (hw : w.im = 0) (D : ι → ℝ)
    (hD : ∀ u, ‖heatAmp w (A u)‖ ≤ D u) :
    (heatGramTermAt a (∑ u, x u • A u) (∑ u, x u • A u) w).re ≤
      ∑ u, ‖x u‖ ^ 2 * (Fintype.card ι * D u ^ 2 * Real.exp (-(a * w.re))) := by
  rw [re_heatGramTermAt_of_im_eq_zero a _ hw, heatAmp_sum_smul]
  have h1 : ‖∑ u, x u * heatAmp w (A u)‖ ≤ ∑ u, ‖x u‖ * D u := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hD u) (norm_nonneg _)
  have h2 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun u => ‖x u‖ * D u)
  rw [Finset.card_univ] at h2
  have h3 : ‖∑ u, x u * heatAmp w (A u)‖ ^ 2 ≤ Fintype.card ι * ∑ u, ‖x u‖ ^ 2 * D u ^ 2 := by
    calc ‖∑ u, x u * heatAmp w (A u)‖ ^ 2 ≤ (∑ u, ‖x u‖ * D u) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ Fintype.card ι * ∑ u, (‖x u‖ * D u) ^ 2 := h2
      _ = Fintype.card ι * ∑ u, ‖x u‖ ^ 2 * D u ^ 2 := by simp only [mul_pow]
  calc Real.exp (-(a * w.re)) * ‖∑ u, x u * heatAmp w (A u)‖ ^ 2
      ≤ Real.exp (-(a * w.re)) * (Fintype.card ι * ∑ u, ‖x u‖ ^ 2 * D u ^ 2) :=
        mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
    _ = ∑ u, ‖x u‖ ^ 2 * (Fintype.card ι * D u ^ 2 * Real.exp (-(a * w.re))) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun u _ => by ring

/-- **Termwise bound.**  `F` contains every upper frequency; the weights `A_u` vanish at `v, v̄` for
`v ≠ u`, are bounded by `D_u` on the real line, and have rank-two contribution `R_u ≤ 0` at `u`;
`q_u` is a copy with frequency `u`. -/
theorem re_heatGramTermAt_sum_le {a : ℝ} {F : Finset ℂ}
    (hF : ∀ q : XiZeroCopy, 0 < (xiHeatFrequency q).im → xiHeatFrequency q ∈ F)
    (hFim : ∀ v ∈ F, 0 < v.im) (A : F → HeatWeights) (D R : F → ℝ) (qs : F → XiZeroCopy)
    (hqs : ∀ u, xiHeatFrequency (qs u) = u)
    (hvan : ∀ u v : F, u ≠ v →
      heatAmp v (A u) = 0 ∧ heatAmp ((starRingEnd ℂ) v) (A u) = 0)
    (hD : ∀ u (w : ℂ), w.im = 0 → ‖heatAmp w (A u)‖ ≤ D u)
    (hR : ∀ u : F, (heatGramTermAt a (A u) (A u) u).re = R u) (hR0 : ∀ u, R u ≤ 0)
    (x : F → ℂ) (q : XiZeroCopy) :
    (heatGramTermAt a (∑ u, x u • A u) (∑ u, x u • A u) (xiHeatFrequency q)).re ≤
      ∑ u, ‖x u‖ ^ 2 * (F.card * D u ^ 2 * Real.exp (-(a * (xiHeatFrequency q).re)) +
        if q = qs u then R u else 0) := by
  classical
  set w := xiHeatFrequency q with hw
  have hP : ∀ u : F, 0 ≤ (F.card : ℝ) * D u ^ 2 * Real.exp (-(a * w.re)) := fun u => by
    positivity
  have hnot : ∀ u : F, q = qs u → 0 < w.im := fun u hqu => by
    have h := hqs u
    rw [← hqu] at h
    rw [hw, h]
    exact hFim u u.2
  have hoff : ∀ v : F,
      (∀ u, u ≠ v → heatAmp w (A u) = 0 ∧ heatAmp ((starRingEnd ℂ) w) (A u) = 0) →
      (heatGramTermAt a (A v) (A v) w).re = R v → (∀ u, u ≠ v → q ≠ qs u) →
      (heatGramTermAt a (∑ u, x u • A u) (∑ u, x u • A u) w).re ≤
        ∑ u, ‖x u‖ ^ 2 * (F.card * D u ^ 2 * Real.exp (-(a * w.re)) +
          if q = qs u then R u else 0) := by
    intro v hv hRv hq
    rw [heatGramTermAt_sum_eq_of_vanish a A x v w hv, re_ofReal_mul, hRv,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ v)]
    have hrest : 0 ≤ ∑ u ∈ Finset.univ.erase v, ‖x u‖ ^ 2 *
        (F.card * D u ^ 2 * Real.exp (-(a * w.re)) + if q = qs u then R u else 0) := by
      refine Finset.sum_nonneg fun u hu => ?_
      rw [if_neg (hq u (Finset.ne_of_mem_erase hu)), add_zero]
      exact mul_nonneg (by positivity) (hP u)
    have hv' : R v ≤ F.card * D v ^ 2 * Real.exp (-(a * w.re)) + if q = qs v then R v else 0 := by
      split_ifs
      · linarith [hP v]
      · linarith [hP v, hR0 v]
    have := mul_le_mul_of_nonneg_left hv' (by positivity : (0 : ℝ) ≤ ‖x v‖ ^ 2)
    linarith
  rcases lt_trichotomy w.im 0 with him | him | him
  · have hmem : (starRingEnd ℂ) w ∈ F := by
      have h := hF (xiZeroCopyLineConjEquiv q)
        (by rw [xiHeatFrequency_lineConj, Complex.conj_im]; linarith)
      rwa [xiHeatFrequency_lineConj] at h
    refine hoff ⟨(starRingEnd ℂ) w, hmem⟩ (fun u hu => ?_) ?_ (fun u _ hqu => ?_)
    · have h := hvan u ⟨(starRingEnd ℂ) w, hmem⟩ hu
      simp only [Complex.conj_conj] at h
      exact ⟨h.2, h.1⟩
    · have h1 : heatGramTermAt a (A ⟨(starRingEnd ℂ) w, hmem⟩) (A ⟨(starRingEnd ℂ) w, hmem⟩) w =
          (starRingEnd ℂ) (heatGramTermAt a (A ⟨(starRingEnd ℂ) w, hmem⟩)
            (A ⟨(starRingEnd ℂ) w, hmem⟩) ((starRingEnd ℂ) w)) := by
        rw [← heatGramTermAt_conj, Complex.conj_conj]
      rw [h1, Complex.conj_re]
      exact hR _
    · have := hnot u hqu
      linarith
  · have hle := re_heatGramTermAt_sum_le_of_im_eq_zero a A x him D (fun u => hD u w him)
    rw [Fintype.card_coe] at hle
    refine hle.trans (Finset.sum_le_sum fun u _ => ?_)
    have hne : q ≠ qs u := fun hqu => by
      have := hnot u hqu
      linarith
    rw [if_neg hne, add_zero]
  · refine hoff ⟨w, hF q him⟩ (fun u hu => ?_) ?_ (fun u hu hqu => hu ?_)
    · have h := hvan u ⟨w, hF q him⟩ hu
      dsimp only at h
      exact h
    · have h := hR ⟨w, hF q him⟩
      dsimp only at h
      exact h
    · apply Subtype.ext
      rw [← hqs u, ← hqu]

/-- **Summed bound.** -/
theorem re_heatGram_sum_le {a : ℝ} (ha : 0 < a) {F : Finset ℂ}
    (hF : ∀ q : XiZeroCopy, 0 < (xiHeatFrequency q).im → xiHeatFrequency q ∈ F)
    (hFim : ∀ v ∈ F, 0 < v.im) (A : F → HeatWeights) (D R : F → ℝ) (qs : F → XiZeroCopy)
    (hqs : ∀ u, xiHeatFrequency (qs u) = u)
    (hvan : ∀ u v : F, u ≠ v →
      heatAmp v (A u) = 0 ∧ heatAmp ((starRingEnd ℂ) v) (A u) = 0)
    (hD : ∀ u (w : ℂ), w.im = 0 → ‖heatAmp w (A u)‖ ≤ D u)
    (hR : ∀ u : F, (heatGramTermAt a (A u) (A u) u).re = R u) (hR0 : ∀ u, R u ≤ 0)
    (x : F → ℂ) :
    (heatGram a (∑ u, x u • A u) (∑ u, x u • A u)).re ≤
      ∑ u, ‖x u‖ ^ 2 * (F.card * D u ^ 2 *
        (∑' q : XiZeroCopy, Real.exp (-(a * (xiHeatFrequency q).re))) + R u) := by
  classical
  have hS : Summable fun q : XiZeroCopy => Real.exp (-(a * (xiHeatFrequency q).re)) := by
    have h := (summable_exp_neg_mul_xiHeatFrequency (τ := (a : ℂ)) (by simpa using ha)).norm
    refine h.congr fun q => ?_
    rw [Complex.norm_exp]
    congr 1
    simp
  have hg : ∀ u : F, Summable fun q : XiZeroCopy => ‖x u‖ ^ 2 *
      (F.card * D u ^ 2 * Real.exp (-(a * (xiHeatFrequency q).re)) +
        if q = qs u then R u else 0) :=
    fun u => ((hS.mul_left _).add (hasSum_ite_eq (qs u) (R u)).summable).mul_left _
  have hsre : Summable fun q : XiZeroCopy =>
      (heatGramTermAt a (∑ u, x u • A u) (∑ u, x u • A u) (xiHeatFrequency q)).re :=
    (summable_heatGramTermAt ha _ _).mapL Complex.reCLM
  rw [heatGram_eq_tsum ha, Complex.re_tsum (summable_heatGramTermAt ha _ _)]
  refine (Summable.tsum_le_tsum
    (fun q => re_heatGramTermAt_sum_le hF hFim A D R qs hqs hvan hD hR hR0 x q) hsre
    (summable_sum fun u _ => hg u)).trans (le_of_eq ?_)
  rw [Summable.tsum_finsetSum fun u _ => hg u]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [tsum_mul_left, Summable.tsum_add (hS.mul_left _) (hasSum_ite_eq (qs u) (R u)).summable,
    tsum_mul_left, (hasSum_ite_eq (qs u) (R u)).tsum_eq]

/-- **Lower bound.**  If the set of upper off-line frequencies is finite, some subspace of dimension
`#U` is negative definite for `Q_a`. -/
theorem exists_heatGram_negative_subspace {a : ℝ} (ha : 0 < a) (hU : xiUpperFrequencies.Finite) :
    ∃ V : Submodule ℂ HeatWeights, Module.finrank ℂ V = hU.toFinset.card ∧
      ∀ c ∈ V, c ≠ 0 → (heatGram a c c).re < 0 := by
  classical
  set F := hU.toFinset with hFdef
  have hFmem : ∀ w, w ∈ F ↔ w ∈ xiUpperFrequencies := fun w => hU.mem_toFinset
  have hFim : ∀ v ∈ F, 0 < v.im := fun v hv => by
    obtain ⟨q, -, h⟩ := (hFmem v).1 hv
    exact h
  have hF : ∀ q : XiZeroCopy, 0 < (xiHeatFrequency q).im → xiHeatFrequency q ∈ F :=
    fun q hq => (hFmem _).2 ⟨q, rfl, hq⟩
  have hqs : ∀ u : F, ∃ q : XiZeroCopy, xiHeatFrequency q = u := fun u => by
    obtain ⟨q, hq, -⟩ := (hFmem u).1 u.2
    exact ⟨q, hq⟩
  choose qs hqs using hqs
  -- the killer scale
  set Rn := ∑ v ∈ F, ‖v‖ with hRn
  have hRn0 : 0 ≤ Rn := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hnormF : ∀ v ∈ F, ‖v‖ ≤ Rn := fun v hv =>
    Finset.single_le_sum (f := fun v => ‖v‖) (fun _ _ => norm_nonneg _) hv
  set ℓ := 1 / (1 + 2 * Rn) with hℓ
  have hℓpos : 0 < ℓ := by positivity
  have hsmall : ∀ x y : ℂ, ‖x‖ ≤ Rn → ‖y‖ ≤ Rn → ℓ * ‖x - y‖ < 2 * Real.pi := by
    intro x y hx hy
    have h1 : ‖x - y‖ ≤ 2 * Rn := (norm_sub_le x y).trans (by linarith)
    have h2 : ℓ * ‖x - y‖ ≤ ℓ * (2 * Rn) := mul_le_mul_of_nonneg_left h1 hℓpos.le
    have h3 : ℓ * (2 * Rn) < 1 := by
      rw [hℓ, div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
      linarith
    linarith [Real.pi_gt_three]
  -- killers
  set K : F → HeatWeights := fun u => heatKiller ℓ F u with hK
  have hKvan : ∀ u v : F, u ≠ v →
      heatAmp v (K u) = 0 ∧ heatAmp ((starRingEnd ℂ) v) (K u) = 0 := fun u v huv =>
    heatAmp_killer_eq_zero v.2 (fun h => huv (Subtype.ext h).symm)
  have hKne : ∀ u : F, heatAmp u (K u) ≠ 0 ∧ heatAmp ((starRingEnd ℂ) u) (K u) ≠ 0 := by
    intro u
    have hu := hFim u u.2
    have hnu : ‖(u : ℂ)‖ ≤ Rn := hnormF u u.2
    have hncu : ‖(starRingEnd ℂ) (u : ℂ)‖ ≤ Rn := by rw [Complex.norm_conj]; exact hnu
    have hnv : ∀ v ∈ F.erase (u : ℂ), ‖v‖ ≤ Rn ∧ ‖(starRingEnd ℂ) v‖ ≤ Rn := fun v hv =>
      ⟨hnormF v (Finset.mem_of_mem_erase hv),
        by rw [Complex.norm_conj]; exact hnormF v (Finset.mem_of_mem_erase hv)⟩
    constructor
    · refine heatAmp_killer_ne_zero hℓpos
        (fun v hv => ⟨Finset.ne_of_mem_erase hv, fun h => ?_⟩)
        (fun v hv => ⟨hsmall _ _ (hnv v hv).1 hnu, hsmall _ _ (hnv v hv).2 hnu⟩)
      have := hFim v (Finset.mem_of_mem_erase hv)
      have h2 := congrArg Complex.im h
      rw [Complex.conj_im] at h2
      linarith
    · refine heatAmp_killer_ne_zero hℓpos (fun v hv => ⟨fun h => ?_, fun h => ?_⟩)
        (fun v hv => ⟨hsmall _ _ (hnv v hv).1 hncu, hsmall _ _ (hnv v hv).2 hncu⟩)
      · have := hFim v (Finset.mem_of_mem_erase hv)
        have h2 := congrArg Complex.im h
        rw [Complex.conj_im] at h2
        linarith
      · exact Finset.ne_of_mem_erase hv ((starRingEnd ℂ).injective h)
  -- constants
  set S := ∑' q : XiZeroCopy, Real.exp (-(a * (xiHeatFrequency q).re)) with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => (Real.exp_pos _).le
  set C : F → ℝ := fun u => heatMass (K u) with hC
  set κ : F → ℂ := fun u => Complex.exp (-(a : ℂ) * u) * heatAmp u (K u) *
    (starRingEnd ℂ) (heatAmp ((starRingEnd ℂ) u) (K u)) with hκ
  have hκne : ∀ u, κ u ≠ 0 := fun u =>
    mul_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) (hKne u).1)
      ((map_ne_zero _).2 (hKne u).2)
  have hpair : ∀ u : F, ∃ L : ℝ, ∃ t : ℂ, ‖t‖ = 1 ∧
      (κ u * heatAmp u (heatMainFactor L t) *
        (starRingEnd ℂ) (heatAmp ((starRingEnd ℂ) u) (heatMainFactor L t))).re ≤
        -(F.card * (2 * C u) ^ 2 * S + 1) :=
    fun u => exists_mainFactor_re_le (hκne u) (hFim u u.2) _
  choose L t ht hLt using hpair
  set A : F → HeatWeights := fun u => heatMainFactor (L u) (t u) * K u with hA
  set R : F → ℝ := fun u => (heatGramTermAt a (A u) (A u) u).re with hR
  have hAvan : ∀ u v : F, u ≠ v →
      heatAmp v (A u) = 0 ∧ heatAmp ((starRingEnd ℂ) v) (A u) = 0 := fun u v huv => by
    refine ⟨?_, ?_⟩
    · show heatAmp v (heatMainFactor (L u) (t u) * K u) = 0
      rw [map_mul, (hKvan u v huv).1, mul_zero]
    · show heatAmp ((starRingEnd ℂ) v) (heatMainFactor (L u) (t u) * K u) = 0
      rw [map_mul, (hKvan u v huv).2, mul_zero]
  have hAD : ∀ u (w : ℂ), w.im = 0 → ‖heatAmp w (A u)‖ ≤ 2 * C u := by
    intro u w hw
    show ‖heatAmp w (heatMainFactor (L u) (t u) * K u)‖ ≤ 2 * heatMass (K u)
    rw [map_mul, norm_mul]
    exact mul_le_mul (norm_heatAmp_mainFactor_le (ht u) hw) (norm_heatAmp_le_heatMass hw _)
      (norm_nonneg _) (by norm_num)
  have hRval : ∀ u : F, R u ≤ -(F.card * (2 * C u) ^ 2 * S + 1) := by
    intro u
    have heq : heatGramTermAt a (A u) (A u) u = κ u * heatAmp u (heatMainFactor (L u) (t u)) *
        (starRingEnd ℂ) (heatAmp ((starRingEnd ℂ) u) (heatMainFactor (L u) (t u))) := by
      show heatGramTermAt a (heatMainFactor (L u) (t u) * K u)
        (heatMainFactor (L u) (t u) * K u) u = _
      simp only [heatGramTermAt, hκ, map_mul]
      ring
    show (heatGramTermAt a (A u) (A u) u).re ≤ _
    rw [heq]
    exact hLt u
  have hR0 : ∀ u, R u ≤ 0 := fun u => by
    have h1 := hRval u
    have h2 : 0 ≤ (F.card : ℝ) * (2 * C u) ^ 2 * S := by positivity
    linarith
  -- the negative-definite family
  have hneg : ∀ x : F → ℂ, x ≠ 0 → (heatGram a (∑ u, x u • A u) (∑ u, x u • A u)).re < 0 := by
    intro x hx
    have hle := re_heatGram_sum_le ha hF hFim A (fun u => 2 * C u) R qs hqs hAvan hAD
      (fun u => rfl) hR0 x
    obtain ⟨u₀, hu₀⟩ : ∃ u, x u ≠ 0 := by
      by_contra h
      push Not at h
      exact hx (funext h)
    have h1 : ∀ u, ‖x u‖ ^ 2 * (F.card * (2 * C u) ^ 2 * S + R u) ≤ -(‖x u‖ ^ 2) := by
      intro u
      have := mul_le_mul_of_nonneg_left
        (show (F.card : ℝ) * (2 * C u) ^ 2 * S + R u ≤ -1 by linarith [hRval u])
        (sq_nonneg ‖x u‖)
      linarith
    have h2 : ∑ u, ‖x u‖ ^ 2 * (F.card * (2 * C u) ^ 2 * S + R u) ≤ -∑ u, ‖x u‖ ^ 2 := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum fun u _ => h1 u
    have h3 : 0 < ∑ u, ‖x u‖ ^ 2 :=
      Finset.sum_pos' (fun u _ => sq_nonneg _) ⟨u₀, Finset.mem_univ _, by positivity⟩
    linarith
  -- the subspace
  set Φ : (F → ℂ) →ₗ[ℂ] HeatWeights := Fintype.linearCombination ℂ A with hΦ
  have hΦapp : ∀ x, Φ x = ∑ u, x u • A u := fun x => Fintype.linearCombination_apply ℂ A x
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hne
    have := hneg x hne
    rw [← hΦapp, hx, heatGram_zero_left, zero_re] at this
    exact lt_irrefl 0 this
  refine ⟨LinearMap.range Φ, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  · rintro c ⟨x, rfl⟩ hc
    have hx : x ≠ 0 := by
      rintro rfl
      exact hc (map_zero Φ)
    rw [hΦapp]
    exact hneg x hx

/-- **The negative index of the vertical heat Gram form.**  If the set `U` of upper off-line
frequencies is finite, then for every `a > 0` the maximal dimension of a subspace on which `Q_a` is
negative definite is exactly `#U`, the number of off-line zero quadruples. -/
theorem heatGram_negativeIndex_eq_card {a : ℝ} (ha : 0 < a) (hU : xiUpperFrequencies.Finite) :
    (∀ V : Submodule ℂ HeatWeights, (∀ c ∈ V, c ≠ 0 → (heatGram a c c).re < 0) →
      Module.finrank ℂ V ≤ hU.toFinset.card) ∧
    ∃ V : Submodule ℂ HeatWeights, Module.finrank ℂ V = hU.toFinset.card ∧
      ∀ c ∈ V, c ≠ 0 → (heatGram a c c).re < 0 :=
  ⟨fun V hV => finrank_le_of_heatGram_neg ha hU V hV, exists_heatGram_negative_subspace ha hU⟩

end

end RHTower
