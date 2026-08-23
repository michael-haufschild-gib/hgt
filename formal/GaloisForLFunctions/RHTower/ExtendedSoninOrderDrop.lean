import GaloisForLFunctions.RHTower.ExtendedSoninDivision
import GaloisForLFunctions.RHTower.MellinApertureIndependence

/-!
# Lowering the order of vanishing at one strip point

Dividing by `(s - ρ)` (Proposition 4.3, `ExtendedSoninDivision`) lowers the order of the continued
Mellin transform at `ρ` by exactly one and leaves every other order untouched.  Iterating gives
Burnol's Lemma 7.4: from one vector of `L_a` whose transform vanishes on a prescribed multiset one
manufactures, for each point `ρ` of the multiset and each jet index `k` below the prescribed
multiplicity, a vector vanishing to order exactly `k` at `ρ` and still to the full order everywhere
else.  That is precisely the statement that the evaluator system is minimal.

## Main results

* `exists_order_drop`
* `exists_order_eq_of_add` — **Lemma 7.4** in jet form.
-/

namespace RHTower

open MeasureTheory Set Complex Filter Topology

open GaloisForLFunctions.HTGeometry

noncomputable section

theorem isOpen_criticalStrip : IsOpen {z : ℂ | 0 < z.re ∧ z.re < 1} :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

theorem isPreconnected_criticalStrip : IsPreconnected {z : ℂ | 0 < z.re ∧ z.re < 1} := by
  have h1 : Convex ℝ {z : ℂ | 0 < z.re} := convex_halfSpace_re_gt 0
  have h2 : Convex ℝ {z : ℂ | z.re < 1} := convex_halfSpace_re_lt 1
  exact (h1.inter h2).isPreconnected

/-- **One division lowers the order at `ρ` by exactly one and preserves all the others.** -/
theorem exists_order_drop {a : ℝ} (ha : 0 < a) {v : SoninL2} {c d : ℂ}
    (hev : v ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary v : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (v : ℝ → ℂ) t = d)
    {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) {n : ℕ}
    (hn : meromorphicOrderAt (extendedMellinContinuation a c d v) ρ
      = (((n : ℤ) + 1 : ℤ) : WithTop ℤ)) :
    ∃ (w : SoninL2) (c' d' : ℂ), w ∈ evenSubspace ∧ w ∈ centralSoninExtendedCarrier a ∧
      (∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval a →
        ((fourierUnitary w : SoninL2) : ℝ → ℂ) x = c') ∧
      (∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (w : ℝ → ℂ) t = d') ∧
      meromorphicOrderAt (extendedMellinContinuation a c' d' w) ρ = ((n : ℤ) : WithTop ℤ) ∧
      ∀ z : ℂ, 0 < z.re → z.re < 1 → z ≠ ρ →
        meromorphicOrderAt (extendedMellinContinuation a c' d' w) z
          = meromorphicOrderAt (extendedMellinContinuation a c d v) z := by
  classical
  have hρ0 : ρ ≠ 0 := by intro h; rw [h] at h0; norm_num at h0
  have hρ1 : ρ ≠ 1 := by intro h; rw [h] at h1; norm_num at h1
  have hana : AnalyticAt ℂ (extendedMellinContinuation a c d v) ρ :=
    analyticAt_extendedMellinContinuation_of_ne ha hev hc hd hρ0 hρ1
  have hvan : extendedMellinContinuation a c d v ρ = 0 := by
    by_contra hne
    have hzero : meromorphicOrderAt (extendedMellinContinuation a c d v) ρ = 0 := by
      rw [hana.meromorphicOrderAt_eq, hana.analyticOrderAt_eq_zero.2 hne]
      simp
    rw [hn] at hzero
    have hcast : ((n : ℤ) + 1) = 0 := by exact_mod_cast hzero
    omega
  obtain ⟨w, c', d', hev', hmem', hc', hd', hmul⟩ :=
    exists_divided_extendedSonin ha hev hc hd h0 h1 hvan
  -- propagate the identity to the whole strip
  have hA1 : AnalyticOnNhd ℂ
      (fun s : ℂ => extendedMellinContinuation a c' d' w s * (s - ρ))
      {z : ℂ | 0 < z.re ∧ z.re < 1} := by
    intro z hz
    have hz0 : z ≠ 0 := by intro h; rw [h] at hz; norm_num at hz
    have hz1 : z ≠ 1 := by intro h; rw [h] at hz; norm_num at hz
    exact (analyticAt_extendedMellinContinuation_of_ne ha hev' hc' hd' hz0 hz1).mul
      (analyticAt_id.sub analyticAt_const)
  have hA2 : AnalyticOnNhd ℂ (extendedMellinContinuation a c d v)
      {z : ℂ | 0 < z.re ∧ z.re < 1} := by
    intro z hz
    have hz0 : z ≠ 0 := by intro h; rw [h] at hz; norm_num at hz
    have hz1 : z ≠ 1 := by intro h; rw [h] at hz; norm_num at hz
    exact analyticAt_extendedMellinContinuation_of_ne ha hev hc hd hz0 hz1
  have hz₀ : ((3 / 4 : ℝ) : ℂ) ∈ {z : ℂ | 0 < z.re ∧ z.re < 1} := by
    constructor <;> simp <;> norm_num
  have hev₀ : (fun s : ℂ => extendedMellinContinuation a c' d' w s * (s - ρ))
      =ᶠ[𝓝 ((3 / 4 : ℝ) : ℂ)] extendedMellinContinuation a c d v := by
    have hopen : IsOpen {z : ℂ | 1 / 2 < z.re ∧ z.re < 1} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    have hmem₀ : ((3 / 4 : ℝ) : ℂ) ∈ {z : ℂ | 1 / 2 < z.re ∧ z.re < 1} := by
      constructor <;> simp <;> norm_num
    filter_upwards [hopen.mem_nhds hmem₀] with z hz
    exact hmul z hz.1 hz.2
  have hall : ∀ z : ℂ, 0 < z.re → z.re < 1 →
      extendedMellinContinuation a c' d' w z * (z - ρ)
        = extendedMellinContinuation a c d v z := fun z hz0 hz1 =>
    hA1.eqOn_of_preconnected_of_eventuallyEq hA2 isPreconnected_criticalStrip hz₀ hev₀ ⟨hz0, hz1⟩
  -- order arithmetic
  have hord : ∀ z : ℂ, 0 < z.re → z.re < 1 →
      meromorphicOrderAt (extendedMellinContinuation a c' d' w) z
          + meromorphicOrderAt (fun s : ℂ => s - ρ) z
        = meromorphicOrderAt (extendedMellinContinuation a c d v) z := by
    intro z hz0 hz1
    have hmero1 : MeromorphicAt (extendedMellinContinuation a c' d' w) z :=
      meromorphicAt_extendedMellinContinuation ha hev' hc' hd' z
    have heq : (fun s : ℂ => extendedMellinContinuation a c' d' w s * (s - ρ))
        =ᶠ[𝓝[≠] z] extendedMellinContinuation a c d v := by
      refine EventuallyEq.filter_mono ?_ nhdsWithin_le_nhds
      filter_upwards [isOpen_criticalStrip.mem_nhds (⟨hz0, hz1⟩ :
        z ∈ {y : ℂ | 0 < y.re ∧ y.re < 1})] with y hy
      exact hall y hy.1 hy.2
    rw [← meromorphicOrderAt_congr heq]
    have hfun : (fun s : ℂ => extendedMellinContinuation a c' d' w s * (s - ρ))
        = extendedMellinContinuation a c' d' w * fun s : ℂ => s - ρ := by
      funext s
      rw [Pi.mul_apply]
    rw [hfun, meromorphicOrderAt_mul hmero1 (analyticAt_sub_const ρ z).meromorphicAt]
  refine ⟨w, c', d', hev', hmem', hc', hd', ?_, ?_⟩
  · have h := hord ρ h0 h1
    rw [meromorphicOrderAt_sub_const_self, hn] at h
    induction hx : meromorphicOrderAt (extendedMellinContinuation a c' d' w) ρ with
    | top =>
        rw [hx, top_add] at h
        first
          | exact absurd h.symm WithTop.coe_ne_top
          | exact absurd h WithTop.top_ne_coe
          | simp [WithTop.top_ne_coe] at h
          | exact (by cases h)
    | coe m =>
        rw [hx] at h
        have hm : m + 1 = (n : ℤ) + 1 := by exact_mod_cast h
        have : m = (n : ℤ) := by omega
        rw [this]
  · intro z hz0 hz1 hzρ
    have h := hord z hz0 hz1
    rw [meromorphicOrderAt_sub_const_of_ne hzρ, add_zero] at h
    exact h

/-- **Burnol's Lemma 7.4, in jet form.**  If the continued Mellin transform of a vector of `L_a`
vanishes to order `k + j` at a strip point `ρ`, then `L_a` contains a vector whose transform
vanishes to order *exactly* `k` at `ρ` and has the same order at every other point of the strip. -/
theorem exists_order_eq_of_add {a : ℝ} (ha : 0 < a) {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (k : ℕ) : ∀ (j : ℕ) (v : SoninL2) (c d : ℂ), v ∈ evenSubspace →
      (∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval a →
        ((fourierUnitary v : SoninL2) : ℝ → ℂ) x = c) →
      (∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (v : ℝ → ℂ) t = d) →
      meromorphicOrderAt (extendedMellinContinuation a c d v) ρ
        = (((k + j : ℕ) : ℤ) : WithTop ℤ) →
      ∃ (w : SoninL2) (c' d' : ℂ), w ∈ evenSubspace ∧ w ∈ centralSoninExtendedCarrier a ∧
        (∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval a →
          ((fourierUnitary w : SoninL2) : ℝ → ℂ) x = c') ∧
        (∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (w : ℝ → ℂ) t = d') ∧
        meromorphicOrderAt (extendedMellinContinuation a c' d' w) ρ = ((k : ℤ) : WithTop ℤ) ∧
        ∀ z : ℂ, 0 < z.re → z.re < 1 → z ≠ ρ →
          meromorphicOrderAt (extendedMellinContinuation a c' d' w) z
            = meromorphicOrderAt (extendedMellinContinuation a c d v) z := by
  intro j
  induction j with
  | zero =>
      intro v c d hev hc hd hord
      refine ⟨v, c, d, hev, mem_centralSoninExtendedCarrier_iff v |>.2 ⟨⟨d, hd⟩, ⟨c, hc⟩⟩,
        hc, hd, ?_, fun z _ _ _ => rfl⟩
      simpa using hord
  | succ j ih =>
      intro v c d hev hc hd hord
      have hstep : meromorphicOrderAt (extendedMellinContinuation a c d v) ρ
          = ((((k + j : ℕ) : ℤ) + 1 : ℤ) : WithTop ℤ) := by
        rw [hord]
        congr 1
      obtain ⟨w₁, c₁, d₁, hev₁, _hmem₁, hc₁, hd₁, hord₁, hother₁⟩ :=
        exists_order_drop ha hev hc hd h0 h1 hstep
      obtain ⟨w, c', d', hev', hmem', hc', hd', hordw, hotherw⟩ :=
        ih w₁ c₁ d₁ hev₁ hc₁ hd₁ hord₁
      refine ⟨w, c', d', hev', hmem', hc', hd', hordw, ?_⟩
      intro z hz0 hz1 hzρ
      rw [hotherw z hz0 hz1 hzρ, hother₁ z hz0 hz1 hzρ]

end

end RHTower
