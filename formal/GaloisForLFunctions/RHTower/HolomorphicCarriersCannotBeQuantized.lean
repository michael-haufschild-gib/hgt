import GaloisForLFunctions.HTGeometry.AutonomousStripSeparant
import Mathlib.Analysis.Complex.Hadamard

/-!
# Holomorphic carriers cannot be quantized

A zero configuration is a finite multiset `Z` in the open critical strip, invariant under the
functional-equation reflection `s ↦ 1 − s` (and, for sesquilinear carriers, under conjugation).
A carrier is computable from an explicit formula when it is a sum of a holomorphic weight over
the configuration, `C(Z) = Σ_{ρ ∈ Z} h(ρ)`, or a sesquilinear sum `Σ_{a, b ∈ Z} k(a, b̄)` with `k`
holomorphic in each slot; Weil quadratic forms and squared explicit sums are of the second kind.

* **Linear rigidity** (`linearCarrier_eq_zero`). If `C` vanishes on every critical pair
  `{½ + it, ½ − it}`, then `C(Z) = 0` for every admissible `Z`. A symmetric configuration only sees
  the symmetrization `h(s) + h(1 − s)`; it vanishes on the critical line, hence on the strip.
* **Sesquilinear rigidity** (`sesquilinearCarrier_eq_zero`). If `C` vanishes on every critical
  configuration, it vanishes on every admissible one. The eight-term symmetrization of `k` under the
  reflections and the slot exchange vanishes on the product of critical lines, hence, one variable at
  a time, on the product of strips; a symmetric configuration only sees that symmetrization.
* **Quantitative tradeoff** (`norm_quartet_le_interp`). If the symmetrized weight is bounded by `ε`
  on `Re s = ½` and by `M` on `Re s = ½ + Δ`, an off-line quartet `ρ, ρ̄, 1 − ρ, 1 − ρ̄` at depth
  `δ = Re ρ − ½ ≤ Δ` carries at most `2 ε^{1−δ/Δ} M^{δ/Δ}` (Hadamard's three lines).
* **No quantum near the line** (`exists_depth_without_quantum`). If `2ε < q`, every quartet close
  enough to the line carries less than `q`.

So a carrier that is exact on critical configurations and built from holomorphic weights sees nothing
off the line, and a carrier whose off-line value is bounded below by a fixed quantum at every depth
must have a weight that is non-holomorphic in the zero or unbounded at the critical line.
-/

noncomputable section

open Complex ComplexConjugate Filter Topology

namespace RHTower

/-- The open critical strip `0 < Re s < 1`, as the strip of half-width `½` about `Re s = ½`. -/
abbrev carrierStrip : Set ℂ := GaloisForLFunctions.verticalStrip (1 / 2) (1 / 2)

theorem one_sub_mem_carrierStrip {s : ℂ} (hs : s ∈ carrierStrip) : 1 - s ∈ carrierStrip := by
  change |(1 - s).re - 1 / 2| < 1 / 2
  change |s.re - 1 / 2| < 1 / 2 at hs
  have h : (1 - s).re - 1 / 2 = -(s.re - 1 / 2) := by simp only [sub_re, one_re]; ring
  rw [h, abs_neg]
  exact hs

theorem mem_carrierStrip_of_re_eq_half {s : ℂ} (hs : s.re = 1 / 2) : s ∈ carrierStrip := by
  change |s.re - 1 / 2| < 1 / 2
  rw [hs]
  norm_num

/-- On the critical line conjugation is the reflection `s ↦ 1 − s`. -/
theorem conj_eq_one_sub_of_re_eq_half {s : ℂ} (hs : s.re = 1 / 2) : conj s = 1 - s := by
  apply Complex.ext
  · simp only [conj_re, sub_re, one_re, hs]
    norm_num
  · simp only [conj_im, sub_im, one_im, zero_sub]

/-- On a configuration invariant under `s ↦ 1 − s`, a weight and its reflection have equal sums. -/
theorem sum_map_one_sub {Z : Multiset ℂ} (hrefl : Z.map (fun z => 1 - z) = Z) (f : ℂ → ℂ) :
    (Z.map fun z => f (1 - z)).sum = (Z.map f).sum := by
  conv_rhs => rw [← hrefl]
  rw [Multiset.map_map]
  rfl

/-! ### Linear carriers -/

/-- The carrier `Σ_{ρ ∈ Z} h(ρ)` of a weight `h`. -/
def linearCarrier (h : ℂ → ℂ) (Z : Multiset ℂ) : ℂ := (Z.map h).sum

/-- **Linear rigidity.** A holomorphic weight whose carrier vanishes on every critical pair has
vanishing carrier on every reflection-invariant configuration in the strip. -/
theorem linearCarrier_eq_zero {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h carrierStrip)
    (hpair : ∀ t : ℝ, linearCarrier h {(1 / 2 : ℂ) + t * I, (1 / 2 : ℂ) - t * I} = 0)
    {Z : Multiset ℂ} (hZ : ∀ z ∈ Z, z ∈ carrierStrip)
    (hrefl : Z.map (fun z => 1 - z) = Z) :
    linearCarrier h Z = 0 := by
  set Φ : ℂ → ℂ := fun s => h s + h (1 - s) with hΦdef
  have hΦ : DifferentiableOn ℂ Φ carrierStrip :=
    hh.add (hh.comp ((differentiableOn_const 1).sub differentiableOn_id)
      (fun s hs => one_sub_mem_carrierStrip hs))
  -- the symmetrized weight vanishes on the critical line, hence on the strip
  have hline : ∀ t : ℝ, Φ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) = 0 := by
    intro t
    have h0 := hpair t
    simp only [linearCarrier, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.sum_cons, Multiset.sum_singleton] at h0
    have h1 : (1 : ℂ) - (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) = (1 / 2 : ℂ) - t * I := by
      push_cast
      ring
    simp only [hΦdef, h1]
    push_cast
    exact h0
  have hzero := GaloisForLFunctions.eqZero_of_eqZero_line (by norm_num) hΦ hline
  -- a symmetric configuration only sees the symmetrization
  have hsum : linearCarrier h Z + linearCarrier h Z = (Z.map Φ).sum := by
    simp only [linearCarrier, hΦdef, Multiset.sum_map_add]
    rw [sum_map_one_sub hrefl h]
  have hΦZ : (Z.map Φ).sum = 0 :=
    Multiset.sum_eq_zero fun x hx => by
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hx
      exact hzero z (hZ z hz)
  rw [hΦZ] at hsum
  linear_combination hsum / 2

/-! ### Sesquilinear carriers -/

/-- The sesquilinear carrier `Σ_{a, b ∈ Z} k(a, b̄)`. -/
def sesquilinearCarrier (k : ℂ → ℂ → ℂ) (Z : Multiset ℂ) : ℂ :=
  (Z.map fun a => (Z.map fun b => k a (conj b)).sum).sum

/-- The cross term `Σ_{a ∈ A, b ∈ B} k(a, b̄)`. -/
def sesquilinearCross (k : ℂ → ℂ → ℂ) (A B : Multiset ℂ) : ℂ :=
  (A.map fun a => (B.map fun b => k a (conj b)).sum).sum

theorem sesquilinearCarrier_add (k : ℂ → ℂ → ℂ) (A B : Multiset ℂ) :
    sesquilinearCarrier k (A + B) = sesquilinearCarrier k A + sesquilinearCarrier k B +
      (sesquilinearCross k A B + sesquilinearCross k B A) := by
  simp only [sesquilinearCarrier, sesquilinearCross, Multiset.map_add, Multiset.sum_add,
    Multiset.sum_map_add]
  ring

/-- The symmetrization of a kernel under `s ↦ 1 − s` in each slot and the slot exchange
`(s, w) ↦ (1 − w, 1 − s)`. -/
def reflectionSymmetrization (k : ℂ → ℂ → ℂ) (s w : ℂ) : ℂ :=
  k s w + k s (1 - w) + k (1 - s) w + k (1 - s) (1 - w) +
    (k (1 - w) (1 - s) + k (1 - w) s + k w (1 - s) + k w s)

/-- The critical pair `{s, 1 − s}`. -/
def criticalPair (s : ℂ) : Multiset ℂ := {s, 1 - s}

theorem criticalPair_reflect (s : ℂ) :
    (criticalPair s).map (fun z => 1 - z) = criticalPair s := by
  simp only [criticalPair, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    sub_sub_cancel]
  exact Multiset.cons_swap _ _ _

theorem criticalPair_re {s : ℂ} (hs : s.re = 1 / 2) : ∀ z ∈ criticalPair s, z.re = 1 / 2 := by
  intro z hz
  simp only [criticalPair, Multiset.insert_eq_cons, Multiset.mem_cons,
    Multiset.mem_singleton] at hz
  rcases hz with rfl | rfl
  · exact hs
  · simp only [sub_re, one_re, hs]
    norm_num

/-- For critical points the two cross terms of their pairs add up to the symmetrization. -/
theorem sesquilinearCross_criticalPair_add (k : ℂ → ℂ → ℂ) {s w : ℂ} (hs : s.re = 1 / 2)
    (hw : w.re = 1 / 2) :
    sesquilinearCross k (criticalPair s) (criticalPair w) +
        sesquilinearCross k (criticalPair w) (criticalPair s) =
      reflectionSymmetrization k s w := by
  have hcs := conj_eq_one_sub_of_re_eq_half hs
  have hcw := conj_eq_one_sub_of_re_eq_half hw
  have hcs' : conj (1 - s) = s := by rw [map_sub, map_one, hcs]; ring
  have hcw' : conj (1 - w) = w := by rw [map_sub, map_one, hcw]; ring
  simp only [sesquilinearCross, criticalPair, Multiset.insert_eq_cons, Multiset.map_cons,
    Multiset.map_singleton, Multiset.sum_cons, Multiset.sum_singleton, hcs, hcw, hcs', hcw',
    reflectionSymmetrization]
  ring

/-- A carrier vanishing on critical configurations has symmetrization vanishing on the product of
critical lines. -/
theorem reflectionSymmetrization_eq_zero_on_line {k : ℂ → ℂ → ℂ}
    (hcrit : ∀ Z : Multiset ℂ, (∀ z ∈ Z, z.re = 1 / 2) → Z.map (fun z => 1 - z) = Z →
      sesquilinearCarrier k Z = 0)
    {s w : ℂ} (hs : s.re = 1 / 2) (hw : w.re = 1 / 2) :
    reflectionSymmetrization k s w = 0 := by
  have hP : ∀ u : ℂ, u.re = 1 / 2 → sesquilinearCarrier k (criticalPair u) = 0 := fun u hu =>
    hcrit (criticalPair u) (criticalPair_re hu) (criticalPair_reflect u)
  have hsum := hcrit (criticalPair s + criticalPair w)
    (fun z hz => (Multiset.mem_add.mp hz).elim (criticalPair_re hs z) (criticalPair_re hw z))
    (by rw [Multiset.map_add, criticalPair_reflect, criticalPair_reflect])
  rw [sesquilinearCarrier_add, hP s hs, hP w hw, sesquilinearCross_criticalPair_add k hs hw]
    at hsum
  simpa using hsum

theorem differentiableOn_reflectionSymmetrization_left {k : ℂ → ℂ → ℂ}
    (hk₁ : ∀ w ∈ carrierStrip, DifferentiableOn ℂ (fun s => k s w) carrierStrip)
    (hk₂ : ∀ s ∈ carrierStrip, DifferentiableOn ℂ (k s) carrierStrip)
    {w : ℂ} (hw : w ∈ carrierStrip) :
    DifferentiableOn ℂ (fun s => reflectionSymmetrization k s w) carrierStrip := by
  have hw' := one_sub_mem_carrierStrip hw
  have hσ : DifferentiableOn ℂ (fun s : ℂ => 1 - s) carrierStrip :=
    (differentiableOn_const 1).sub differentiableOn_id
  have hmaps : Set.MapsTo (fun s : ℂ => 1 - s) carrierStrip carrierStrip :=
    fun s hs => one_sub_mem_carrierStrip hs
  exact ((((hk₁ w hw).add (hk₁ (1 - w) hw')).add ((hk₁ w hw).comp hσ hmaps)).add
      ((hk₁ (1 - w) hw').comp hσ hmaps)).add
    (((((hk₂ (1 - w) hw').comp hσ hmaps).add (hk₂ (1 - w) hw')).add
      ((hk₂ w hw).comp hσ hmaps)).add (hk₂ w hw))

theorem differentiableOn_reflectionSymmetrization_right {k : ℂ → ℂ → ℂ}
    (hk₁ : ∀ w ∈ carrierStrip, DifferentiableOn ℂ (fun s => k s w) carrierStrip)
    (hk₂ : ∀ s ∈ carrierStrip, DifferentiableOn ℂ (k s) carrierStrip)
    {s : ℂ} (hs : s ∈ carrierStrip) :
    DifferentiableOn ℂ (fun w => reflectionSymmetrization k s w) carrierStrip := by
  have hs' := one_sub_mem_carrierStrip hs
  have hσ : DifferentiableOn ℂ (fun s : ℂ => 1 - s) carrierStrip :=
    (differentiableOn_const 1).sub differentiableOn_id
  have hmaps : Set.MapsTo (fun s : ℂ => 1 - s) carrierStrip carrierStrip :=
    fun s hs => one_sub_mem_carrierStrip hs
  exact ((((hk₂ s hs).add ((hk₂ s hs).comp hσ hmaps)).add (hk₂ (1 - s) hs')).add
      ((hk₂ (1 - s) hs').comp hσ hmaps)).add
    (((((hk₁ (1 - s) hs').comp hσ hmaps).add ((hk₁ s hs).comp hσ hmaps)).add
      (hk₁ (1 - s) hs')).add (hk₁ s hs))

/-- **Sesquilinear rigidity.** A sesquilinear carrier with kernel holomorphic in each slot that
vanishes on every critical configuration vanishes on every configuration in the strip invariant under
`s ↦ 1 − s` and conjugation. -/
theorem sesquilinearCarrier_eq_zero {k : ℂ → ℂ → ℂ}
    (hk₁ : ∀ w ∈ carrierStrip, DifferentiableOn ℂ (fun s => k s w) carrierStrip)
    (hk₂ : ∀ s ∈ carrierStrip, DifferentiableOn ℂ (k s) carrierStrip)
    (hcrit : ∀ Z : Multiset ℂ, (∀ z ∈ Z, z.re = 1 / 2) → Z.map (fun z => 1 - z) = Z →
      sesquilinearCarrier k Z = 0)
    {Z : Multiset ℂ} (hZ : ∀ z ∈ Z, z ∈ carrierStrip)
    (hrefl : Z.map (fun z => 1 - z) = Z) (hconj : Z.map conj = Z) :
    sesquilinearCarrier k Z = 0 := by
  -- the symmetrization vanishes on the product of strips, one variable at a time
  have hline : ∀ w : ℂ, w.re = 1 / 2 → ∀ s ∈ carrierStrip,
      reflectionSymmetrization k s w = 0 := by
    intro w hw
    refine GaloisForLFunctions.eqZero_of_eqZero_line (by norm_num)
      (differentiableOn_reflectionSymmetrization_left hk₁ hk₂
        (mem_carrierStrip_of_re_eq_half hw)) ?_
    intro t
    exact reflectionSymmetrization_eq_zero_on_line hcrit (by simp) hw
  have hstrip : ∀ s ∈ carrierStrip, ∀ w ∈ carrierStrip,
      reflectionSymmetrization k s w = 0 := by
    intro s hs
    refine GaloisForLFunctions.eqZero_of_eqZero_line (by norm_num)
      (differentiableOn_reflectionSymmetrization_right hk₁ hk₂ hs) ?_
    intro t
    exact hline _ (by simp) s hs
  -- conjugation invariance removes the conjugate in the second slot
  set S : (ℂ → ℂ → ℂ) → ℂ := fun f => (Z.map fun a => (Z.map fun w => f a w).sum).sum
    with hSdef
  have hD : sesquilinearCarrier k Z = S k := by
    simp only [sesquilinearCarrier, hSdef]
    congr 1
    apply Multiset.map_congr rfl
    intro a _
    conv_rhs => rw [← hconj]
    rw [Multiset.map_map]
    rfl
  have hleft : ∀ f : ℂ → ℂ → ℂ, S (fun a w => f (1 - a) w) = S f := fun f => by
    simp only [hSdef]
    exact sum_map_one_sub hrefl (fun a => (Z.map fun w => f a w).sum)
  have hright : ∀ f : ℂ → ℂ → ℂ, S (fun a w => f a (1 - w)) = S f := fun f => by
    simp only [hSdef]
    congr 1
    apply Multiset.map_congr rfl
    intro a _
    exact sum_map_one_sub hrefl (f a)
  have hswap : ∀ f : ℂ → ℂ → ℂ, S (fun a w => f w a) = S f := fun f => by
    simp only [hSdef]
    exact Multiset.sum_map_sum_map Z Z
  -- each of the eight terms of the symmetrization has the same double sum
  have e2 : S (fun a w => k a (1 - w)) = S k := hright k
  have e3 : S (fun a w => k (1 - a) w) = S k := hleft k
  have e4 : S (fun a w => k (1 - a) (1 - w)) = S k :=
    (hleft (fun a w => k a (1 - w))).trans e2
  have e5 : S (fun a w => k (1 - w) (1 - a)) = S k :=
    (hswap (fun a w => k (1 - a) (1 - w))).trans e4
  have e6 : S (fun a w => k (1 - w) a) = S k := (hswap (fun a w => k (1 - a) w)).trans e3
  have e7 : S (fun a w => k w (1 - a)) = S k := (hswap (fun a w => k a (1 - w))).trans e2
  have e8 : S (fun a w => k w a) = S k := hswap k
  have h8 : S (reflectionSymmetrization k) =
      S k + S (fun a w => k a (1 - w)) + S (fun a w => k (1 - a) w) +
        S (fun a w => k (1 - a) (1 - w)) +
      (S (fun a w => k (1 - w) (1 - a)) + S (fun a w => k (1 - w) a) +
        S (fun a w => k w (1 - a)) + S (fun a w => k w a)) := by
    simp only [hSdef, reflectionSymmetrization, Multiset.sum_map_add]
  rw [e2, e3, e4, e5, e6, e7, e8] at h8
  have h0 : S (reflectionSymmetrization k) = 0 := by
    simp only [hSdef]
    refine Multiset.sum_eq_zero fun x hx => ?_
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hx
    refine Multiset.sum_eq_zero fun y hy => ?_
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hy
    exact hstrip a (hZ a ha) w (hZ w hw)
  rw [hD]
  linear_combination (h0 - h8) / 8

/-! ### The quantitative tradeoff -/

/-- The reflection-symmetrized weight `h(s) + h(1 − s)`. -/
def reflectedWeight (h : ℂ → ℂ) (s : ℂ) : ℂ := h s + h (1 - s)

/-- An off-line quartet sees the symmetrized weight at `ρ` and at `ρ̄`. -/
theorem quartet_eq (h : ℂ → ℂ) (ρ : ℂ) :
    h ρ + h (conj ρ) + h (1 - ρ) + h (1 - conj ρ) =
      reflectedWeight h ρ + reflectedWeight h (conj ρ) := by
  simp only [reflectedWeight]
  ring

/-- **Three-lines tradeoff.** If the symmetrized weight is bounded by `ε` on the critical line and
by `M` on `Re s = ½ + Δ`, the quartet of a zero at depth `δ = Re ρ − ½ ≤ Δ` carries at most
`2 ε^{1−δ/Δ} M^{δ/Δ}`. -/
theorem norm_quartet_le_interp {h : ℂ → ℂ} {Δ ε M : ℝ} (hΔ : 0 < Δ)
    (hd : DiffContOnCl ℂ (reflectedWeight h)
      (Complex.HadamardThreeLines.verticalStrip (1 / 2) (1 / 2 + Δ)))
    (hB : BddAbove ((norm ∘ reflectedWeight h) ''
      Complex.HadamardThreeLines.verticalClosedStrip (1 / 2) (1 / 2 + Δ)))
    (hε : ∀ z : ℂ, z.re = 1 / 2 → ‖reflectedWeight h z‖ ≤ ε)
    (hM : ∀ z : ℂ, z.re = 1 / 2 + Δ → ‖reflectedWeight h z‖ ≤ M)
    {ρ : ℂ} (hρ₁ : 1 / 2 ≤ ρ.re) (hρ₂ : ρ.re ≤ 1 / 2 + Δ) :
    ‖h ρ + h (conj ρ) + h (1 - ρ) + h (1 - conj ρ)‖ ≤
      2 * (ε ^ (1 - (ρ.re - 1 / 2) / Δ) * M ^ ((ρ.re - 1 / 2) / Δ)) := by
  have hlu : (1 / 2 : ℝ) < 1 / 2 + Δ := by linarith
  have hwidth : (1 / 2 + Δ) - 1 / 2 = Δ := by ring
  have bound : ∀ z : ℂ, z.re = ρ.re → ‖reflectedWeight h z‖ ≤
      ε ^ (1 - (ρ.re - 1 / 2) / Δ) * M ^ ((ρ.re - 1 / 2) / Δ) := by
    intro z hz
    have hmem : z ∈ Complex.HadamardThreeLines.verticalClosedStrip (1 / 2) (1 / 2 + Δ) := by
      change z.re ∈ Set.Icc (1 / 2 : ℝ) (1 / 2 + Δ)
      rw [hz]
      exact ⟨hρ₁, hρ₂⟩
    have h3 := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip' hlu hmem
      hd hB (fun z hz => hε z hz) (fun z hz => hM z hz)
    rwa [hwidth, hz] at h3
  rw [quartet_eq]
  have h1 := bound ρ rfl
  have h2 := bound (conj ρ) (by simp)
  calc _ ≤ ‖reflectedWeight h ρ‖ + ‖reflectedWeight h (conj ρ)‖ := norm_add_le _ _
    _ ≤ _ := by linarith

/-- **No quantum near the line.** If the on-line bound `ε` is below half a quantum `q`, every quartet
close enough to the critical line carries less than `q`. -/
theorem exists_depth_without_quantum {h : ℂ → ℂ} {Δ ε M q : ℝ} (hΔ : 0 < Δ) (hε0 : 0 < ε)
    (hM0 : 0 < M) (hq : 2 * ε < q)
    (hd : DiffContOnCl ℂ (reflectedWeight h)
      (Complex.HadamardThreeLines.verticalStrip (1 / 2) (1 / 2 + Δ)))
    (hB : BddAbove ((norm ∘ reflectedWeight h) ''
      Complex.HadamardThreeLines.verticalClosedStrip (1 / 2) (1 / 2 + Δ)))
    (hε : ∀ z : ℂ, z.re = 1 / 2 → ‖reflectedWeight h z‖ ≤ ε)
    (hM : ∀ z : ℂ, z.re = 1 / 2 + Δ → ‖reflectedWeight h z‖ ≤ M) :
    ∃ δ₀ > 0, ∀ ρ : ℂ, 1 / 2 ≤ ρ.re → ρ.re < 1 / 2 + δ₀ → ρ.re ≤ 1 / 2 + Δ →
      ‖h ρ + h (conj ρ) + h (1 - ρ) + h (1 - conj ρ)‖ < q := by
  set g : ℝ → ℝ := fun θ => 2 * (ε ^ (1 - θ) * M ^ θ) with hg
  have hcont : ContinuousAt g 0 := by
    have h1 : ContinuousAt (fun θ : ℝ => ε ^ (1 - θ)) 0 :=
      ContinuousAt.comp (f := fun θ : ℝ => 1 - θ) (Real.continuousAt_const_rpow hε0.ne')
        (continuousAt_const.sub continuousAt_id)
    have h2 : ContinuousAt (fun θ : ℝ => M ^ θ) 0 := Real.continuousAt_const_rpow hM0.ne'
    exact continuousAt_const.mul (h1.mul h2)
  have hg0 : g 0 < q := by
    simp only [hg, sub_zero, Real.rpow_one, Real.rpow_zero, mul_one]
    exact hq
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.mp (hcont.eventually (gt_mem_nhds hg0))
  refine ⟨η * Δ, mul_pos hη hΔ, fun ρ hρ₁ hρ₂ hρ₃ => ?_⟩
  have hθ : dist ((ρ.re - 1 / 2) / Δ) 0 < η := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (by linarith) hΔ.le), div_lt_iff₀ hΔ]
    linarith
  exact (norm_quartet_le_interp hΔ hd hB hε hM hρ₁ hρ₃).trans_lt (hball hθ)

end RHTower

#print axioms RHTower.linearCarrier_eq_zero
#print axioms RHTower.sesquilinearCarrier_eq_zero
#print axioms RHTower.norm_quartet_le_interp
#print axioms RHTower.exists_depth_without_quantum
