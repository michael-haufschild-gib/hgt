import GaloisForLFunctions.BiScaleUncertainty.PowerOrbitLaw

/-!
# Finite designs with exact vanishing cosine moments

A *design* is a finite list of weighted angles `(w, θ)`. Its cosine moments are
`Σ w cos(jθ)`. For the power-grid moment problem one needs atomic measures whose cosine moments
vanish *exactly* at finitely many frequencies, with folded-symbol value close to that of an
arbitrary probability measure on the circle.

* **Quadrature designs** (`dirDesign`, `uniDesign`). On `N > 2K` equally spaced angles the
  weights `(1 ± cos(jθ_k))/N` have cosine moment `±½` at `j` and `0` at every other frequency
  in `[1, K]`; equal weights have all these moments zero.
* **Approximation** (`exists_design_approx`). The vector of finitely many moments and the value of
  a probability measure lies in the closed convex hull of the curve they trace, so a design matches
  them up to any `η > 0`.
* **Exactification** (`exists_design_exact`). Mixing a small multiple of quadrature designs
  removes the residual moments exactly, at a cost `O(λ)` in value.
-/

open MeasureTheory Set Complex
open Zeta23
open RHTower RHTower.WeilOneSided RHTower.PrimeCirclePeriodization RHTower.BlindPrimePowerSlack
local notation "π" => Real.pi

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-! ### 1. Designs -/

/-- Total weight of a design. -/
def designMass (D : List (ℝ × ℝ)) : ℝ := (D.map Prod.fst).sum

/-- The cosine moment `Σ w cos(jθ)`. -/
def designMoment (D : List (ℝ × ℝ)) (j : ℕ) : ℝ := (D.map fun a => a.1 * Real.cos (j * a.2)).sum

/-- The value `Σ w F(θ)` of an observable `P` of the circle. -/
def designValue (P : AddCircle (2 * π) → ℝ) (D : List (ℝ × ℝ)) : ℝ :=
  (D.map fun a => a.1 * P (a.2 : AddCircle (2 * π))).sum

/-- Weights scaled by `t`. -/
def designScale (t : ℝ) (D : List (ℝ × ℝ)) : List (ℝ × ℝ) := D.map fun a => (t * a.1, a.2)

theorem designMass_append (D E : List (ℝ × ℝ)) :
    designMass (D ++ E) = designMass D + designMass E := by
  simp [designMass]

theorem designMoment_append (D E : List (ℝ × ℝ)) (j : ℕ) :
    designMoment (D ++ E) j = designMoment D j + designMoment E j := by
  simp [designMoment]

theorem designValue_append (P : AddCircle (2 * π) → ℝ) (D E : List (ℝ × ℝ)) :
    designValue P (D ++ E) = designValue P D + designValue P E := by
  simp [designValue]

theorem designMass_scale (t : ℝ) (D : List (ℝ × ℝ)) :
    designMass (designScale t D) = t * designMass D := by
  simp only [designMass, designScale, List.map_map, Function.comp_def]
  rw [List.sum_map_mul_left]

theorem designMoment_scale (t : ℝ) (D : List (ℝ × ℝ)) (j : ℕ) :
    designMoment (designScale t D) j = t * designMoment D j := by
  simp only [designMoment, designScale, List.map_map, Function.comp_def, mul_assoc]
  rw [List.sum_map_mul_left]

theorem designValue_scale (P : AddCircle (2 * π) → ℝ) (t : ℝ) (D : List (ℝ × ℝ)) :
    designValue P (designScale t D) = t * designValue P D := by
  simp only [designValue, designScale, List.map_map, Function.comp_def, mul_assoc]
  rw [List.sum_map_mul_left]

theorem designScale_nonneg {t : ℝ} (ht : 0 ≤ t) {D : List (ℝ × ℝ)} (hD : ∀ a ∈ D, 0 ≤ a.1) :
    ∀ a ∈ designScale t D, 0 ≤ a.1 := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  exact mul_nonneg ht (hD b hb)

theorem designValue_le_of_le {P : AddCircle (2 * π) → ℝ} {B : ℝ} (hP : ∀ z, P z ≤ B)
    {D : List (ℝ × ℝ)} (hD : ∀ a ∈ D, 0 ≤ a.1) : designValue P D ≤ B * designMass D := by
  induction D with
  | nil => simp [designValue, designMass]
  | cons a D ih =>
    have ha := hD a (List.mem_cons_self ..)
    have ht := ih fun b hb => hD b (List.mem_cons_of_mem _ hb)
    simp only [designValue, designMass, List.map_cons, List.sum_cons] at ht ⊢
    nlinarith [mul_le_mul_of_nonneg_left (hP (a.2 : AddCircle (2 * π))) ha]

/-! ### 2. Quadrature designs -/

/-- Equal weights `1/N` on the angles `2πk/N`. -/
def uniDesign (N : ℕ) : List (ℝ × ℝ) :=
  (List.range N).map fun k : ℕ => ((1 : ℝ) / N, 2 * π * k / N)

/-- Weights `(1 + s cos(jθ_k))/N` on the angles `θ_k = 2πk/N`. -/
def dirDesign (N j : ℕ) (s : ℝ) : List (ℝ × ℝ) :=
  (List.range N).map fun k : ℕ => ((1 + s * Real.cos (j * (2 * π * k / N))) / N, 2 * π * k / N)

private theorem list_sum_range {β : Type*} [AddCommMonoid β] (g : ℕ → β) (n : ℕ) :
    ((List.range n).map g).sum = ∑ k ∈ Finset.range n, g k := by
  induction n with
  | zero => rw [List.range_zero, List.map_nil, List.sum_nil, Finset.range_zero, Finset.sum_empty]
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ,
      List.map_singleton, List.sum_singleton]

/-- `Σ_{k<N} cos(2πmk/N) = 0` for `1 ≤ m < N`. -/
theorem sum_cos_quadrature_eq_zero {N m : ℕ} (hm1 : 1 ≤ m) (hmN : m < N) :
    ∑ k ∈ Finset.range N, Real.cos (m * (2 * π * k / N)) = 0 := by
  have h := sum_cos_orbit_eq_zero (d := N) (j := m) (by omega)
    (fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)) 0
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1; ring

theorem designMass_uniDesign {N : ℕ} (hN : 1 ≤ N) : designMass (uniDesign N) = 1 := by
  rw [designMass, uniDesign, List.map_map, list_sum_range]
  simp only [Function.comp_apply, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  field_simp

theorem designMoment_uniDesign {N j : ℕ} (hj1 : 1 ≤ j) (hjN : j < N) :
    designMoment (uniDesign N) j = 0 := by
  rw [designMoment, uniDesign, List.map_map, list_sum_range]
  simp only [Function.comp_apply]
  rw [← Finset.mul_sum, sum_cos_quadrature_eq_zero hj1 hjN, mul_zero]

theorem uniDesign_nonneg (N : ℕ) : ∀ a ∈ uniDesign N, 0 ≤ a.1 := by
  intro a ha
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp ha
  positivity

theorem designMass_dirDesign {N j : ℕ} (hj1 : 1 ≤ j) (hjN : j < N) (s : ℝ) :
    designMass (dirDesign N j s) = 1 := by
  rw [designMass, dirDesign, List.map_map, list_sum_range]
  simp only [Function.comp_apply]
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_cos_quadrature_eq_zero hj1 hjN]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, mul_zero, add_zero]
  have : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  field_simp

/-- The cosine moment of a directional design: `s/2` at `j`, zero at every other frequency of
`[1, K]` when `2K < N`. -/
theorem designMoment_dirDesign {K N j j' : ℕ} (hj1 : 1 ≤ j) (hjK : j ≤ K) (hj'1 : 1 ≤ j')
    (hj'K : j' ≤ K) (hN : 2 * K < N) (s : ℝ) :
    designMoment (dirDesign N j s) j' = if j' = j then s / 2 else 0 := by
  rw [designMoment, dirDesign, List.map_map, list_sum_range]
  simp only [Function.comp_apply]
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have e : ∀ k : ℕ, (1 + s * Real.cos (j * (2 * π * k / N))) / N * Real.cos (j' * (2 * π * k / N)) =
      (1 / N) * Real.cos (j' * (2 * π * k / N)) +
        (s / (2 * N)) * (Real.cos (((j' + j : ℕ) : ℝ) * (2 * π * k / N)) +
          Real.cos ((j' : ℝ) * (2 * π * k / N) - (j : ℝ) * (2 * π * k / N))) := by
    intro k
    push_cast
    rw [show ((j' : ℝ) + j) * (2 * π * k / N) = j' * (2 * π * k / N) + j * (2 * π * k / N) by ring,
      Real.cos_add, Real.cos_sub]
    field_simp
    ring
  simp only [e]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib,
    sum_cos_quadrature_eq_zero hj'1 (by omega), sum_cos_quadrature_eq_zero (by omega) (by omega)]
  by_cases hjj : j' = j
  · subst hjj
    simp only [sub_self, Real.cos_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one, if_true]
    field_simp
    ring
  · rw [if_neg hjj]
    have hdiff : ∀ k : ℕ, Real.cos ((j' : ℝ) * (2 * π * k / N) - (j : ℝ) * (2 * π * k / N)) =
        Real.cos ((Int.natAbs ((j' : ℤ) - j) : ℝ) * (2 * π * k / N)) := by
      intro k
      rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub, Int.cast_natCast, Int.cast_natCast,
        ← sub_mul]
      rcases abs_choice ((j' : ℝ) - j) with h | h <;> rw [h]
      rw [neg_mul, Real.cos_neg]
    simp only [hdiff]
    rw [sum_cos_quadrature_eq_zero (by omega) (by omega)]
    ring

theorem dirDesign_nonneg {N j : ℕ} {s : ℝ} (hs : |s| ≤ 1) : ∀ a ∈ dirDesign N j s, 0 ≤ a.1 := by
  intro a ha
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp ha
  have h1 := Real.abs_cos_le_one (j * (2 * π * k / N))
  have h2 : |s * Real.cos (j * (2 * π * k / N))| ≤ 1 := by
    rw [abs_mul]; nlinarith [abs_nonneg s, abs_nonneg (Real.cos (j * (2 * π * k / N)))]
  have := (abs_le.mp h2).1
  apply div_nonneg (by linarith) (Nat.cast_nonneg _)

/-! ### 3. Approximation by designs -/

theorem designMoment_flatMap (L : List ℕ) (g : ℕ → List (ℝ × ℝ)) (j : ℕ) :
    designMoment (L.flatMap g) j = (L.map fun i => designMoment (g i) j).sum := by
  induction L with
  | nil => simp [designMoment]
  | cons a L ih => rw [List.flatMap_cons, designMoment_append, ih, List.map_cons, List.sum_cons]

theorem designMass_flatMap (L : List ℕ) (g : ℕ → List (ℝ × ℝ)) :
    designMass (L.flatMap g) = (L.map fun i => designMass (g i)).sum := by
  induction L with
  | nil => simp [designMass]
  | cons a L ih => rw [List.flatMap_cons, designMass_append, ih, List.map_cons, List.sum_cons]

theorem designValue_flatMap (P : AddCircle (2 * π) → ℝ) (L : List ℕ) (g : ℕ → List (ℝ × ℝ)) :
    designValue P (L.flatMap g) = (L.map fun i => designValue P (g i)).sum := by
  induction L with
  | nil => simp [designValue]
  | cons a L ih => rw [List.flatMap_cons, designValue_append, ih, List.map_cons, List.sum_cons]

theorem flatMap_nonneg {L : List ℕ} {g : ℕ → List (ℝ × ℝ)} (hg : ∀ i ∈ L, ∀ a ∈ g i, 0 ≤ a.1) :
    ∀ a ∈ L.flatMap g, 0 ≤ a.1 := by
  intro a ha
  obtain ⟨i, hi, ha⟩ := List.mem_flatMap.mp ha
  exact hg i hi a ha

/-- **Approximation by designs.** Finitely many cosine moments and the value of a continuous
observable of a probability measure on the circle are matched by a design up to any `η > 0`. -/
theorem exists_design_approx (ν : Measure (AddCircle (2 * π))) [IsProbabilityMeasure ν]
    (js : List ℕ) {P : AddCircle (2 * π) → ℝ} (hP : Continuous P) {η : ℝ} (hη : 0 < η) :
    ∃ D : List (ℝ × ℝ), (∀ a ∈ D, 0 ≤ a.1) ∧ designMass D = 1 ∧
      (∀ j ∈ js, |designMoment D j - ∫ z, circleCos j z ∂ν| < η) ∧
      |designValue P D - ∫ z, P z ∂ν| < η := by
  classical
  set m := js.length with hm
  let Ψ : AddCircle (2 * π) → (Fin (m + 1) → ℝ) := fun z i =>
    if h : (i : ℕ) < m then circleCos (js.get ⟨i, h⟩) z else P z
  have hΨc : ∀ i, Continuous fun z => Ψ z i := by
    intro i
    by_cases h : (i : ℕ) < m
    · simp only [Ψ, dif_pos h]; exact continuous_circleCos _
    · simp only [Ψ, dif_neg h]; exact hP
  have hΨi : ∀ i, Integrable (fun z => Ψ z i) ν := fun i =>
    (BoundedContinuousFunction.mkOfCompact ⟨_, hΨc i⟩).integrable ν
  have hΨint : Integrable Ψ ν := Integrable.of_eval hΨi
  set S : Set (Fin (m + 1) → ℝ) := closure (convexHull ℝ (Set.range Ψ)) with hS
  have hmem : ∫ z, Ψ z ∂ν ∈ S :=
    Convex.integral_mem (convex_convexHull ℝ _).closure isClosed_closure
      (Filter.Eventually.of_forall fun z => subset_closure (subset_convexHull ℝ _ ⟨z, rfl⟩))
      hΨint
  obtain ⟨p, hp, hdist⟩ := Metric.mem_closure_iff.mp hmem η hη
  obtain ⟨ι, hι, w, y, hw0, hw1, hy, hpw⟩ := mem_convexHull_iff_exists_fintype.mp hp
  choose z hz using hy
  choose θ hθ using fun i => QuotientAddGroup.mk_surjective (z i)
  let D : List (ℝ × ℝ) := (Finset.univ : Finset ι).toList.map fun i => (w i, θ i)
  have hcoord : ∀ k : Fin (m + 1), |p k - (∫ z, Ψ z ∂ν) k| < η := by
    intro k
    have := (norm_le_pi_norm (p - ∫ z, Ψ z ∂ν) k).trans_lt (by rwa [dist_comm, dist_eq_norm] at hdist)
    simpa [Real.norm_eq_abs] using this
  have hpk : ∀ k : Fin (m + 1), p k = ∑ i, w i * Ψ (θ i : AddCircle (2 * π)) k := by
    intro k
    rw [← hpw]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hθ i, hz i]
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
    exact hw0 i
  · rw [designMass, List.map_map, Function.comp_def, Finset.sum_map_toList]
    exact hw1
  · intro j hj
    obtain ⟨⟨k, hk⟩, hkj⟩ := List.mem_iff_get.mp hj
    have h1 := hcoord ⟨k, by omega⟩
    rw [hpk, eval_integral hΨi] at h1
    have hΨk : ∀ z, Ψ z ⟨k, by omega⟩ = circleCos j z := by
      intro z
      simp only [Ψ]
      rw [dif_pos hk]
      congr 1
    simp only [hΨk] at h1
    have e : designMoment D j = ∑ i, w i * circleCos j (θ i : AddCircle (2 * π)) := by
      rw [designMoment, List.map_map, Function.comp_def, Finset.sum_map_toList]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [circleCos_coe]
    rwa [e]
  · have h1 := hcoord ⟨m, by omega⟩
    rw [hpk, eval_integral hΨi] at h1
    simp only [Ψ, lt_irrefl, dif_neg, not_false_eq_true] at h1
    have e : designValue P D = ∑ i, w i * P (θ i : AddCircle (2 * π)) := by
      rw [designValue, List.map_map, Function.comp_def, Finset.sum_map_toList]
    rwa [e]

/-! ### 4. Exact vanishing -/

/-- **Exactification.** If a probability measure on the circle has vanishing cosine moments at
the finitely many frequencies of `J ⊆ [1, K]`, a design of mass one has exactly vanishing moments
there and value at most `∫ P dν + ε`. -/
theorem exists_design_exact (ν : Measure (AddCircle (2 * π))) [IsProbabilityMeasure ν]
    {K : ℕ} (J : Finset ℕ) (hJ : ∀ j ∈ J, 1 ≤ j ∧ j ≤ K)
    (hν : ∀ j ∈ J, ∫ z, circleCos j z ∂ν = 0) {P : AddCircle (2 * π) → ℝ} (hP : Continuous P)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ D : List (ℝ × ℝ), (∀ a ∈ D, 0 ≤ a.1) ∧ designMass D = 1 ∧
      (∀ j ∈ J, designMoment D j = 0) ∧ designValue P D ≤ ∫ z, P z ∂ν + ε := by
  classical
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hP.continuousOn
  have hB' : ∀ z, |P z| ≤ B := fun z => by rw [← Real.norm_eq_abs]; exact hB z (Set.mem_univ z)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB' 0)
  set lam : ℝ := min (1 / 2) (ε / (4 * B + 2)) with hlam
  have hlam0 : 0 < lam := lt_min (by norm_num) (by positivity)
  have hlam1 : lam ≤ 1 / 2 := min_le_left _ _
  have hlamε : lam * (4 * B + 2) ≤ ε := by
    have := min_le_right (1 / 2 : ℝ) (ε / (4 * B + 2))
    rw [← hlam] at this
    rwa [le_div_iff₀ (by positivity)] at this
  set m := J.card with hm
  set η : ℝ := min (ε / 2) (lam / (2 * (m + 1))) with hη
  have hη0 : 0 < η := lt_min (by positivity) (by positivity)
  obtain ⟨D₁, hD₁0, hD₁1, hD₁m, hD₁v⟩ := exists_design_approx ν J.toList hP hη0
  set c : ℕ → ℝ := fun j => -((1 - lam) / lam) * designMoment D₁ j with hc
  have hcb : ∀ j ∈ J, 2 * |c j| ≤ 1 / (m + 1) := by
    intro j hj
    have h1 := hD₁m j (Finset.mem_toList.mpr hj)
    rw [hν j hj, sub_zero] at h1
    have hηl : η ≤ lam / (2 * (m + 1)) := min_le_right _ _
    simp only [hc, abs_mul, abs_neg]
    rw [abs_of_nonneg (by have : 0 ≤ 1 - lam := by linarith
                          positivity)]
    have h2 : (1 - lam) / lam * |designMoment D₁ j| ≤ (1 / lam) * η := by
      apply mul_le_mul (div_le_div_of_nonneg_right (by linarith) hlam0.le) h1.le (abs_nonneg _)
        (by positivity)
    have h3 : (1 / lam) * η ≤ 1 / (2 * (m + 1)) := by
      rw [one_div_mul_eq_div, div_le_iff₀ hlam0]
      calc η ≤ lam / (2 * (m + 1)) := hηl
        _ = 1 / (2 * (m + 1)) * lam := by ring
    have : (0 : ℝ) < m + 1 := by positivity
    calc 2 * ((1 - lam) / lam * |designMoment D₁ j|) ≤ 2 * (1 / (2 * (m + 1))) := by linarith
      _ = 1 / (m + 1) := by field_simp
  set sg : ℕ → ℝ := fun j => if 0 ≤ c j then 1 else -1 with hsg
  have hsgc : ∀ j, |c j| * sg j = c j := by
    intro j; simp only [hsg]; split_ifs with h
    · rw [abs_of_nonneg h, mul_one]
    · rw [abs_of_neg (lt_of_not_ge h)]; ring
  have hsg1 : ∀ j, |sg j| ≤ 1 := by intro j; simp only [hsg]; split_ifs <;> norm_num
  set N : ℕ := 2 * K + 1 with hN
  set tot : ℝ := ∑ j ∈ J, 2 * |c j| with htot
  have htot1 : tot ≤ 1 := by
    calc tot ≤ ∑ _j ∈ J, (1 : ℝ) / (m + 1) := Finset.sum_le_sum fun j hj => hcb j hj
      _ = m / (m + 1) := by rw [Finset.sum_const, nsmul_eq_mul, ← hm]; ring
      _ ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  set C : List (ℝ × ℝ) := J.toList.flatMap (fun j => designScale (2 * |c j|) (dirDesign N j (sg j)))
    ++ designScale (1 - tot) (uniDesign N) with hC
  have hC0 : ∀ a ∈ C, 0 ≤ a.1 := by
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact flatMap_nonneg (fun j _ => designScale_nonneg (by positivity)
        (dirDesign_nonneg (hsg1 j))) a h
    · exact designScale_nonneg (by linarith) (uniDesign_nonneg N) a h
  have hCmass : designMass C = 1 := by
    rw [hC, designMass_append, designMass_flatMap, designMass_scale, designMass_uniDesign
      (by omega), Finset.sum_map_toList]
    have : ∑ j ∈ J, designMass (designScale (2 * |c j|) (dirDesign N j (sg j))) = tot := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [designMass_scale, designMass_dirDesign (hJ j hj).1 (by have := (hJ j hj).2; omega),
        mul_one]
    rw [this]; ring
  have hCmom : ∀ j' ∈ J, designMoment C j' = c j' := by
    intro j' hj'
    rw [hC, designMoment_append, designMoment_flatMap, designMoment_scale,
      designMoment_uniDesign (hJ j' hj').1 (by have := (hJ j' hj').2; omega), mul_zero, add_zero,
      Finset.sum_map_toList]
    have e : ∀ j ∈ J, designMoment (designScale (2 * |c j|) (dirDesign N j (sg j))) j' =
        if j' = j then |c j| * sg j else 0 := by
      intro j hj
      rw [designMoment_scale, designMoment_dirDesign (hJ j hj).1 (hJ j hj).2 (hJ j' hj').1
        (hJ j' hj').2 (by omega)]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl e, Finset.sum_ite_eq J j' (fun j => |c j| * sg j), if_pos hj',
      hsgc]
  set D : List (ℝ × ℝ) := designScale (1 - lam) D₁ ++ designScale lam C with hD
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact designScale_nonneg (by linarith) hD₁0 a h
    · exact designScale_nonneg hlam0.le hC0 a h
  · rw [hD, designMass_append, designMass_scale, designMass_scale, hD₁1, hCmass]; ring
  · intro j hj
    rw [hD, designMoment_append, designMoment_scale, designMoment_scale, hCmom j hj, hc]
    field_simp
    ring
  · rw [hD, designValue_append, designValue_scale, designValue_scale]
    have hCv : designValue P C ≤ B * designMass C :=
      designValue_le_of_le (fun z => (le_abs_self _).trans (hB' z)) hC0
    rw [hCmass, mul_one] at hCv
    have hv1 := (abs_lt.mp hD₁v).2
    have hint : -B ≤ ∫ z, P z ∂ν := by
      have := abs_integral_le_integral_abs (f := P) (μ := ν)
      have h2 : ∫ z, |P z| ∂ν ≤ B := by
        have := integral_mono ((BoundedContinuousFunction.mkOfCompact ⟨_, hP.abs⟩).integrable ν)
          (integrable_const B) (fun z => hB' z)
        simpa using this
      linarith [(abs_le.mp (this.trans h2)).1]
    have hηε : η ≤ ε / 2 := min_le_left _ _
    nlinarith

end

end GaloisForLFunctions.BiScaleUncertainty
