import GaloisForLFunctions.RHTower.XiTwoPortProducerEdges
import GaloisForLFunctions.RHTower.FinitePeeling
import GaloisForLFunctions.RHTower.EntireArgumentVariationRectangle
import GaloisForLFunctions.HTGeometry.RectangleBoundaryPole

/-!
# Peeling the zeros on the left edge of a rectangle

The argument principle needs a function that does not vanish on the boundary. The left edge of
the rectangles used for the two-port producer lies on `Re s = ½ + h`, where both `B_h` and `ξ` may
vanish. Those zeros are finitely many in a window. Dividing out the polynomial
`P(z) = ∏ (z − w)^{m_w}` over them leaves a cofactor that does not vanish on the edge.

* `logDeriv_linePoly`, `three_edge_linePoly`: if every `w` lies on the left edge strictly between
  the heights, the three remaining edges of `P` contribute exactly `π Σ m_w`. Each edge integral is
  the simple-pole variation `simplePole_three_edge_variation`.
* `linePoly_line`: on the line, `P(c + it) = i^M ∏ (t − Im w)^{m_w}` with `M = Σ m_w`.
* `re_logDeriv_eq_zero_of_line_real`: if `F` is real on the line and `F = P·G`, then `G` has
  constant phase there, so `Re(G'/G)(c + it) = 0`.
* `exists_level_finset`: a continuous phase that advances by `Δ` crosses at least `Δ/π − 1`
  levels where the cosine vanishes, at distinct interior points.
* `natCast_le_analyticOrderAt_twoPort`: on the line, `B_h` vanishes at least to the order of `ξ`.
  This uses `ξ(s − 2h) = conj ξ(2c − s̄)`.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-- The polynomial vanishing exactly at the points of `S`, with multiplicities `m`. -/
def linePoly (S : Finset ℂ) (m : ℂ → ℕ) (z : ℂ) : ℂ := ∏ w ∈ S, (z - w) ^ m w

theorem differentiable_linePoly (S : Finset ℂ) (m : ℂ → ℕ) : Differentiable ℂ (linePoly S m) := by
  intro z
  unfold linePoly
  exact DifferentiableAt.fun_finsetProd fun w _ => (differentiableAt_id.sub_const w).pow _

theorem linePoly_ne_zero {S : Finset ℂ} {m : ℂ → ℕ} {z : ℂ} (hz : ∀ w ∈ S, z ≠ w) :
    linePoly S m z ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun w hw => pow_ne_zero _ (sub_ne_zero.mpr (hz w hw))

theorem logDeriv_linePoly {S : Finset ℂ} {m : ℂ → ℕ} {z : ℂ} (hz : ∀ w ∈ S, z ≠ w) :
    logDeriv (linePoly S m) z = ∑ w ∈ S, (m w : ℂ) * (z - w)⁻¹ := by
  unfold linePoly
  rw [logDeriv_prod (f := fun w z => (z - w) ^ m w)
    (fun w hw => pow_ne_zero _ (sub_ne_zero.mpr (hz w hw)))
    (fun w _ => (differentiableAt_id.sub_const w).pow _)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hp := logDeriv_fun_pow (f := fun z : ℂ => z - w) (x := z) (by fun_prop) (m w)
  rw [hp, logDeriv_apply]
  simp

/-- **The three remaining edges of a left-edge polynomial.** -/
theorem three_edge_linePoly {c d T₁ T₂ : ℝ} (hcd : c < d) (S : Finset ℂ) (m : ℂ → ℕ)
    (hS : ∀ w ∈ S, w.re = c ∧ T₁ < w.im ∧ w.im < T₂) :
    (∫ t in T₁..T₂, (logDeriv (linePoly S m) ((d : ℂ) + t * I)).re)
      + (∫ x in c..d, (logDeriv (linePoly S m) ((x : ℂ) + T₁ * I)).im)
      - (∫ x in c..d, (logDeriv (linePoly S m) ((x : ℂ) + T₂ * I)).im)
      = Real.pi * ∑ w ∈ S, (m w : ℝ) := by
  have hR : ∀ w ∈ S, ∀ t : ℝ, (d : ℂ) + t * I - w ≠ 0 := by
    intro w hw t h0
    have := congrArg Complex.re h0
    simp [(hS w hw).1] at this; linarith
  have hB : ∀ w ∈ S, ∀ x : ℝ, (x : ℂ) + T₁ * I - w ≠ 0 := by
    intro w hw x h0
    have := congrArg Complex.im h0
    simp at this; linarith [(hS w hw).2.1]
  have hT : ∀ w ∈ S, ∀ x : ℝ, (x : ℂ) + T₂ * I - w ≠ 0 := by
    intro w hw x h0
    have := congrArg Complex.im h0
    simp at this; linarith [(hS w hw).2.2]
  -- pointwise expansions
  have eR : ∀ t : ℝ, (logDeriv (linePoly S m) ((d : ℂ) + t * I)).re =
      ∑ w ∈ S, (m w : ℝ) * (((d : ℂ) + t * I - w)⁻¹).re := by
    intro t
    rw [logDeriv_linePoly (fun w hw => sub_ne_zero.mp (hR w hw t)), Complex.re_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp [Complex.mul_re]
  have eB : ∀ x : ℝ, (logDeriv (linePoly S m) ((x : ℂ) + T₁ * I)).im =
      ∑ w ∈ S, (m w : ℝ) * (((x : ℂ) + T₁ * I - w)⁻¹).im := by
    intro x
    rw [logDeriv_linePoly (fun w hw => sub_ne_zero.mp (hB w hw x)), Complex.im_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp [Complex.mul_im]
  have eT : ∀ x : ℝ, (logDeriv (linePoly S m) ((x : ℂ) + T₂ * I)).im =
      ∑ w ∈ S, (m w : ℝ) * (((x : ℂ) + T₂ * I - w)⁻¹).im := by
    intro x
    rw [logDeriv_linePoly (fun w hw => sub_ne_zero.mp (hT w hw x)), Complex.im_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp [Complex.mul_im]
  simp_rw [eR, eB, eT]
  -- integrability of each summand
  have iR : ∀ w ∈ S, IntervalIntegrable
      (fun t : ℝ => (m w : ℝ) * (((d : ℂ) + t * I - w)⁻¹).re) volume T₁ T₂ := by
    intro w hw
    refine (Continuous.intervalIntegrable ?_ _ _)
    exact continuous_const.mul (Complex.continuous_re.comp
      ((by fun_prop : Continuous fun t : ℝ => (d : ℂ) + t * I - w).inv₀ (hR w hw)))
  have iB : ∀ w ∈ S, IntervalIntegrable
      (fun x : ℝ => (m w : ℝ) * (((x : ℂ) + T₁ * I - w)⁻¹).im) volume c d := by
    intro w hw
    refine (Continuous.intervalIntegrable ?_ _ _)
    exact continuous_const.mul (Complex.continuous_im.comp
      ((by fun_prop : Continuous fun x : ℝ => (x : ℂ) + T₁ * I - w).inv₀ (hB w hw)))
  have iT : ∀ w ∈ S, IntervalIntegrable
      (fun x : ℝ => (m w : ℝ) * (((x : ℂ) + T₂ * I - w)⁻¹).im) volume c d := by
    intro w hw
    refine (Continuous.intervalIntegrable ?_ _ _)
    exact continuous_const.mul (Complex.continuous_im.comp
      ((by fun_prop : Continuous fun x : ℝ => (x : ℂ) + T₂ * I - w).inv₀ (hT w hw)))
  rw [intervalIntegral.integral_finsetSum iR, intervalIntegral.integral_finsetSum iB,
    intervalIntegral.integral_finsetSum iT, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun w hw => ?_
  simp only [intervalIntegral.integral_const_mul]
  have hw' : w = (c : ℂ) + (w.im : ℂ) * I := by
    apply Complex.ext <;> simp [(hS w hw).1]
  have key := simplePole_three_edge_variation hcd (hS w hw).2.1 (hS w hw).2.2
  rw [← hw'] at key
  rw [show (m w : ℝ) * (∫ t in T₁..T₂, (((d : ℂ) + t * I - w)⁻¹).re)
      + (m w : ℝ) * (∫ x in c..d, (((x : ℂ) + T₁ * I - w)⁻¹).im)
      - (m w : ℝ) * (∫ x in c..d, (((x : ℂ) + T₂ * I - w)⁻¹).im)
      = (m w : ℝ) * ((∫ t in T₁..T₂, (((d : ℂ) + t * I - w)⁻¹).re)
        + (∫ x in c..d, (((x : ℂ) + T₁ * I - w)⁻¹).im)
        - (∫ x in c..d, (((x : ℂ) + T₂ * I - w)⁻¹).im)) by ring, key]
  ring

/-- On the line, `P(c + it) = i^M ∏ (t − Im w)^{m_w}`. -/
theorem linePoly_line {c : ℝ} {S : Finset ℂ} (m : ℂ → ℕ) (hS : ∀ w ∈ S, w.re = c) (t : ℝ) :
    linePoly S m ((c : ℂ) + t * I) =
      I ^ (∑ w ∈ S, m w) * ((∏ w ∈ S, (t - w.im) ^ m w : ℝ) : ℂ) := by
  unfold linePoly
  have e : ∀ w ∈ S, ((c : ℂ) + t * I - w) ^ m w = I ^ m w * (((t - w.im) ^ m w : ℝ) : ℂ) := by
    intro w hw
    have : (c : ℂ) + t * I - w = I * ((t - w.im : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hS w hw]
    rw [this, mul_pow]; push_cast; ring
  rw [Finset.prod_congr rfl e, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  push_cast
  ring

/-- **A cofactor of a line-real function has constant phase on the line.** -/
theorem re_logDeriv_eq_zero_of_line_real {F G : ℂ → ℂ} {c : ℝ} {S : Finset ℂ} {m : ℂ → ℕ}
    (hG : Differentiable ℂ G)
    (hreal : ∀ t : ℝ, (F ((c : ℂ) + t * I)).im = 0)
    (hS : ∀ w ∈ S, w.re = c)
    (hfac : ∀ z, F z = linePoly S m z * G z)
    {t : ℝ} (hGt : G ((c : ℂ) + t * I) ≠ 0) :
    (logDeriv G ((c : ℂ) + t * I)).re = 0 := by
  classical
  set κ : ℂ := I ^ (∑ w ∈ S, m w) with hκ
  have hκ0 : κ ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
  set φ : ℝ → ℝ := fun u => (κ * G ((c : ℂ) + u * I)).im with hφ
  have hpath : ∀ u : ℝ, HasDerivAt (fun v : ℝ => (c : ℂ) + v * I) I u := by
    intro u; simpa using ((hasDerivAt_id u).ofReal_comp.mul_const I).const_add (c : ℂ)
  have hGd : ∀ u : ℝ, HasDerivAt (fun v : ℝ => κ * G ((c : ℂ) + v * I))
      (κ * (deriv G ((c : ℂ) + u * I) * I)) u := by
    intro u
    have := (hG ((c : ℂ) + u * I)).hasDerivAt.comp u (hpath u)
    exact this.const_mul κ
  have hφc : Continuous φ := by
    have : Continuous fun u : ℝ => κ * G ((c : ℂ) + u * I) :=
      continuous_const.mul (hG.continuous.comp (by fun_prop))
    exact Complex.continuous_im.comp this
  -- `φ` vanishes off the finitely many ordinates of `S`
  have hoff : ∀ u : ℝ, (∀ w ∈ S, u ≠ w.im) → φ u = 0 := by
    intro u hu
    have hne : ∀ w ∈ S, (c : ℂ) + u * I ≠ w := by
      intro w hw h0
      exact hu w hw (by have := congrArg Complex.im h0; simpa using this)
    have hP := linePoly_ne_zero (m := m) hne
    have hline := linePoly_line m hS u
    set p : ℝ := ∏ w ∈ S, (u - w.im) ^ m w
    have hp : (p : ℂ) ≠ 0 := by
      intro h0; rw [hline, h0, mul_zero] at hP; exact hP rfl
    have hGu : κ * G ((c : ℂ) + u * I) = F ((c : ℂ) + u * I) / (p : ℂ) := by
      rw [hfac, hline]; field_simp; rw [hκ]; ring
    simp only [hφ, hGu]
    rw [Complex.div_ofReal_im, hreal u, zero_div]
  have hzero : ∀ u : ℝ, φ u = 0 := by
    intro u
    have hfin : (S.image Complex.im : Set ℝ).Finite := (S.image Complex.im).finite_toSet
    have hev : ∀ᶠ v in 𝓝[≠] u, φ v = 0 := by
      have h1 : ∀ᶠ v in 𝓝[≠] u, v ∉ (S.image Complex.im : Set ℝ) := by
        have := (hfin.subset (Set.sdiff_subset (t := {u}))).isClosed.isOpen_compl.mem_nhds
          (fun h => h.2 (Set.mem_singleton u))
        filter_upwards [nhdsWithin_le_nhds this, self_mem_nhdsWithin] with v hv hvu
        intro hmem; exact hv ⟨hmem, hvu⟩
      filter_upwards [h1] with v hv
      refine hoff v fun w hw h0 => hv ?_
      rw [h0]; exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hw)
    have ht := (hφc.tendsto u).mono_left (nhdsWithin_le_nhds (s := {u}ᶜ))
    exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' (hev.mono fun v hv => hv.symm))
  -- the derivative of the vanishing imaginary part vanishes
  have hderiv0 : (κ * (deriv G ((c : ℂ) + t * I) * I)).im = 0 := by
    have h1 : HasDerivAt φ (κ * (deriv G ((c : ℂ) + t * I) * I)).im t :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hGd t)
    have h2 : HasDerivAt φ 0 t := by
      have : φ = fun _ => (0 : ℝ) := funext hzero
      rw [this]; exact hasDerivAt_const t 0
    exact h1.unique h2
  have hb : (κ * G ((c : ℂ) + t * I)).im = 0 := hzero t
  have hbne : κ * G ((c : ℂ) + t * I) ≠ 0 := mul_ne_zero hκ0 hGt
  set a := κ * (deriv G ((c : ℂ) + t * I) * I)
  set b := κ * G ((c : ℂ) + t * I)
  have hlog : logDeriv G ((c : ℂ) + t * I) = -I * (a / b) := by
    have e1 : a / b = (deriv G ((c : ℂ) + t * I) * I) / G ((c : ℂ) + t * I) :=
      mul_div_mul_left _ _ hκ0
    have e2 : -I * (deriv G ((c : ℂ) + t * I) * I) = deriv G ((c : ℂ) + t * I) := by
      ring_nf; rw [Complex.I_sq]; ring
    rw [e1, logDeriv_apply, mul_div_assoc', e2]
  have ha : a = (a.re : ℂ) := Complex.ext (by simp) (by simp [hderiv0])
  have hb' : b = (b.re : ℂ) := Complex.ext (by simp) (by simp [hb])
  rw [hlog, ha, hb', ← Complex.ofReal_div]
  simp

/-- **Level crossings of a continuous phase.** If `ψ` is continuous on `[T₁, T₂]`, its cosine does
not vanish at the endpoints, and `ψ(T₂) − ψ(T₁) = Δ`, then there are at least `Δ/π − 1` distinct
points of `(T₁, T₂)` where `cos ψ = 0`. -/
theorem exists_level_finset {ψ : ℝ → ℝ} {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂)
    (hψ : ContinuousOn ψ (Icc T₁ T₂))
    (h₁ : Real.cos (ψ T₁) ≠ 0) (h₂ : Real.cos (ψ T₂) ≠ 0) :
    ∃ Λ : Finset ℝ, (∀ t ∈ Λ, t ∈ Ioo T₁ T₂ ∧ Real.cos (ψ t) = 0) ∧
      (ψ T₂ - ψ T₁) / Real.pi - 1 ≤ (Λ.card : ℝ) := by
  classical
  have hπ : 0 < Real.pi := Real.pi_pos
  set Δ := ψ T₂ - ψ T₁ with hΔ
  rcases lt_or_ge Δ Real.pi with hsmall | hbig
  · refine ⟨∅, by simp, ?_⟩
    simp only [Finset.card_empty, Nat.cast_zero]
    rw [sub_nonpos, div_le_one hπ]; exact hsmall.le
  set n : ℕ := ⌊Δ / Real.pi⌋₊ with hn
  set k₀ : ℤ := ⌈(ψ T₁ - Real.pi / 2) / Real.pi⌉ with hk₀
  set ℓ : ℕ → ℝ := fun k => Real.pi / 2 + ((k₀ : ℝ) + k) * Real.pi with hℓ
  have hℓ0 : ψ T₁ ≤ ℓ 0 := by
    have := Int.le_ceil ((ψ T₁ - Real.pi / 2) / Real.pi)
    rw [div_le_iff₀ hπ] at this
    simp only [hℓ, Nat.cast_zero, add_zero]
    linarith
  have hℓ0' : ℓ 0 < ψ T₁ + Real.pi := by
    have := Int.ceil_lt_add_one ((ψ T₁ - Real.pi / 2) / Real.pi)
    rw [div_add' _ _ _ hπ.ne', lt_div_iff₀ hπ] at this
    simp only [hℓ, Nat.cast_zero, add_zero]
    linarith
  have hnΔ : (n : ℝ) * Real.pi ≤ Δ := by
    have := Nat.floor_le (div_nonneg (by linarith) hπ.le : 0 ≤ Δ / Real.pi)
    rw [← hn, le_div_iff₀ hπ] at this; exact this
  have hn1 : Δ / Real.pi - 1 ≤ n := by
    have := Nat.lt_floor_add_one (Δ / Real.pi)
    rw [← hn] at this; linarith
  have hmem : ∀ k ∈ Finset.range n, ∃ t ∈ Icc T₁ T₂, ψ t = ℓ k := by
    intro k hk
    have hk' : (k : ℝ) + 1 ≤ n := by
      have := Finset.mem_range.mp hk; exact_mod_cast this
    have hlo : ψ T₁ ≤ ℓ k := by
      have : ℓ 0 ≤ ℓ k := by simp only [hℓ, Nat.cast_zero, add_zero]; nlinarith
      linarith
    have hhi : ℓ k ≤ ψ T₂ := by
      have e : ℓ k = ℓ 0 + k * Real.pi := by simp only [hℓ, Nat.cast_zero, add_zero]; ring
      have : (k : ℝ) * Real.pi + Real.pi ≤ n * Real.pi := by nlinarith
      rw [e]; linarith
    obtain ⟨t, ht, hψt⟩ := intermediate_value_Icc hT hψ ⟨hlo, hhi⟩
    exact ⟨t, ht, hψt⟩
  choose! τ hτmem hτψ using hmem
  have hcos : ∀ k : ℕ, Real.cos (ℓ k) = 0 := by
    intro k
    rw [Real.cos_eq_zero_iff]
    exact ⟨k₀ + k, by simp only [hℓ]; push_cast; ring⟩
  refine ⟨(Finset.range n).image τ, ?_, ?_⟩
  · intro t ht
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ht
    have hc : Real.cos (ψ (τ k)) = 0 := by rw [hτψ k hk]; exact hcos k
    obtain ⟨hlo, hhi⟩ := hτmem k hk
    refine ⟨⟨lt_of_le_of_ne hlo ?_, lt_of_le_of_ne hhi ?_⟩, hc⟩
    · intro h0; rw [← h0] at hc; exact h₁ hc
    · intro h0; rw [h0] at hc; exact h₂ hc
  · rw [Finset.card_image_of_injOn]
    · simpa using hn1
    · intro k hk k' hk' hkk
      have := congrArg ψ hkk
      rw [hτψ k hk, hτψ k' hk'] at this
      simp only [hℓ] at this
      have : (k : ℝ) = k' := by nlinarith
      exact_mod_cast this

/-- **On the line, `B_h` vanishes at least to the order of `ξ`.** -/
theorem natCast_le_analyticOrderAt_twoPort {h τ : ℝ} {n : ℕ}
    (hn : (n : ℕ∞) ≤ analyticOrderAt xi (((1 / 2 + h : ℝ) : ℂ) + τ * I)) :
    (n : ℕ∞) ≤ analyticOrderAt (twoPort h) (((1 / 2 + h : ℝ) : ℂ) + τ * I) := by
  set w : ℂ := ((1 / 2 + h : ℝ) : ℂ) + τ * I with hw
  set c : ℝ := 1 / 2 + h with hc
  have hxan : ∀ z, AnalyticAt ℂ xi z := fun z =>
    xi_differentiable.differentiableOn.analyticOnNhd isOpen_univ z (mem_univ _)
  obtain ⟨g, hg, hfac⟩ := (natCast_le_analyticOrderAt (hxan w)).mp hn
  -- the reflected factor
  set ĝ : ℂ → ℂ := fun z => (starRingEnd ℂ) (g ((starRingEnd ℂ) (2 * c - z))) with hĝ
  have hreflw : (starRingEnd ℂ) (2 * (c : ℂ) - w) = w := by
    rw [hw]; apply Complex.ext <;> simp; ring
  have hĝan : AnalyticAt ℂ ĝ w := by
    obtain ⟨U, hU, hUo, hgU⟩ : ∃ U ∈ 𝓝 w, IsOpen U ∧ DifferentiableOn ℂ g U := by
      obtain ⟨V, hV, hgV⟩ := hg.exists_mem_nhds_analyticOnNhd
      obtain ⟨U, hUV, hUo, hwU⟩ := mem_nhds_iff.mp hV
      exact ⟨U, hUo.mem_nhds hwU, hUo, (hgV.mono hUV).differentiableOn⟩
    set V : Set ℂ := (fun z => (starRingEnd ℂ) (2 * (c : ℂ) - z)) ⁻¹' U with hV
    have hcont : Continuous fun z : ℂ => (starRingEnd ℂ) (2 * (c : ℂ) - z) := by fun_prop
    have hVo : IsOpen V := hUo.preimage hcont
    have hwV : w ∈ V := by
      show (starRingEnd ℂ) (2 * (c : ℂ) - w) ∈ U
      rw [hreflw]; exact mem_of_mem_nhds hU
    refine DifferentiableOn.analyticAt (s := V) ?_ (hVo.mem_nhds hwV)
    intro z hz
    have hgz : DifferentiableAt ℂ g ((starRingEnd ℂ) (2 * (c : ℂ) - z)) :=
      (hgU _ hz).differentiableAt (hUo.mem_nhds hz)
    have hd := hgz.hasDerivAt.conj_conj
    rw [Complex.conj_conj] at hd
    have hlin : HasDerivAt (fun z : ℂ => 2 * (c : ℂ) - z) (-1) z := by
      simpa using (hasDerivAt_id z).const_sub (2 * (c : ℂ))
    have hcomp := hd.comp z hlin
    have : (⇑(starRingEnd ℂ) ∘ g ∘ ⇑(starRingEnd ℂ)) ∘ (fun z : ℂ => 2 * (c : ℂ) - z) = ĝ := by
      funext z; simp [hĝ, Function.comp]
    rw [this] at hcomp
    exact hcomp.differentiableAt.differentiableWithinAt
  refine (natCast_le_analyticOrderAt ((differentiable_twoPort h).analyticAt w)).mpr
    ⟨fun z => g z + (-1) ^ n * ĝ z, hg.add (analyticAt_const.mul hĝan), ?_⟩
  -- transport the factorisation of `ξ` near `w` to `ξ(· − 2h)` near `w`
  have hcl : Tendsto (fun z : ℂ => (starRingEnd ℂ) (2 * (c : ℂ) - z)) (𝓝 w) (𝓝 w) := by
    have : Continuous fun z : ℂ => (starRingEnd ℂ) (2 * (c : ℂ) - z) := by fun_prop
    have := this.tendsto w
    rwa [hreflw] at this
  filter_upwards [hfac, hcl.eventually hfac] with z h1 h2
  have e2 : xi (z - 2 * h) = (-1) ^ n * ((z - w) ^ n * ĝ z) := by
    have hx : z - 2 * (h : ℂ) = 1 - (starRingEnd ℂ) ((starRingEnd ℂ) (2 * (c : ℂ) - z)) := by
      simp only [Complex.conj_conj, hc]; push_cast; ring
    rw [hx, xi_one_sub, xi_conj, h2, smul_eq_mul, map_mul, map_pow]
    have hc' : (starRingEnd ℂ) ((starRingEnd ℂ) (2 * (c : ℂ) - z) - w) = -(z - w) := by
      rw [map_sub, Complex.conj_conj, hw]; apply Complex.ext <;> simp [hc] <;> ring
    rw [hc', neg_pow]
    simp only [hĝ]
    ring
  simp only [smul_eq_mul] at h1 ⊢
  unfold twoPort
  rw [h1, e2]; ring

end

end RHTower
