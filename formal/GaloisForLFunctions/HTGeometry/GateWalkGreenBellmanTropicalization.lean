import GaloisForLFunctions.HTGeometry.ExactPenaltyCircuitBellman

/-!
# Gate-walk Green sandwich for robust circuit complexity

For a finite nonempty gate dictionary, let `q l` be the uniform fraction of length-`l`
gate words whose endpoint enters a prescribed metric ball.  If `c` is the least word length
that reaches that ball, the geometrically killed Green mass

`(1 - a) * ∑' l, a ^ l * q l`

lies between `(1 - a) * (a / M) ^ c` and `a ^ c`, where `M` is dictionary cardinality.
The result directly connects `approxComplexity` to a local random gate walk: it is not an
abstract wrapper around a pre-assumed probability estimate.
-/

open scoped BigOperators

namespace HTGeometry

/-- Normalized Green mass of a nonnegative length reporter under geometric killing. -/
noncomputable def killedGreen (a : ℝ) (q : ℕ → ℝ) : ℝ :=
  (1 - a) * ∑' l : ℕ, a ^ l * q l

/-- A `[0,1]`-valued reporter is summable against a geometric fugacity below one. -/
theorem summable_weighted_of_unit_bound
    {a : ℝ} {q : ℕ → ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hq0 : ∀ l, 0 ≤ q l) (hq1 : ∀ l, q l ≤ 1) :
    Summable (fun l : ℕ => a ^ l * q l) := by
  have hnorm : ‖a‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg ha0]
    exact ha1
  apply Summable.of_nonneg_of_le (fun l => mul_nonneg (pow_nonneg ha0 _) (hq0 l))
    (fun l => ?_) (summable_geometric_of_norm_lt_one hnorm)
  simpa using mul_le_mul_of_nonneg_left (hq1 l) (pow_nonneg ha0 l)

/-- If the reporter vanishes before `c`, its killed Green mass is at most `a ^ c`. -/
theorem killedGreen_upper
    {a : ℝ} {q : ℕ → ℝ} {c : ℕ}
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hq0 : ∀ l, 0 ≤ q l) (hq1 : ∀ l, q l ≤ 1)
    (hbefore : ∀ l < c, q l = 0) :
    killedGreen a q ≤ a ^ c := by
  have hsum := summable_weighted_of_unit_bound ha0 ha1 hq0 hq1
  have hsplit := hsum.sum_add_tsum_nat_add c
  have hprefix : ∑ l ∈ Finset.range c, a ^ l * q l = 0 := by
    apply Finset.sum_eq_zero
    intro l hl
    rw [hbefore l (Finset.mem_range.mp hl), mul_zero]
  have hrewrite : (∑' l : ℕ, a ^ l * q l) = ∑' k : ℕ, a ^ (k + c) * q (k + c) := by
    linarith
  have hshift : Summable (fun k : ℕ => a ^ (k + c) * q (k + c)) := by
    exact (summable_nat_add_iff c).2 hsum
  have hgeom : Summable (fun k : ℕ => a ^ (k + c)) := by
    have hnorm : ‖a‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg ha0]
      exact ha1
    simpa [pow_add, mul_comm] using
      (summable_geometric_of_norm_lt_one hnorm).mul_left (a ^ c)
  have htail : (∑' k : ℕ, a ^ (k + c) * q (k + c)) ≤ ∑' k : ℕ, a ^ (k + c) := by
    exact hshift.tsum_le_tsum (fun k =>
      mul_le_of_le_one_right (pow_nonneg ha0 _) (hq1 (k + c))) hgeom
  rw [killedGreen, hrewrite]
  have hone : 0 ≤ 1 - a := sub_nonneg.mpr ha1.le
  calc
    (1 - a) * ∑' k : ℕ, a ^ (k + c) * q (k + c)
        ≤ (1 - a) * ∑' k : ℕ, a ^ (k + c) := mul_le_mul_of_nonneg_left htail hone
    _ = a ^ c := by
      rw [show (∑' k : ℕ, a ^ (k + c)) = a ^ c * (1 - a)⁻¹ by
        simp_rw [pow_add]
        rw [tsum_mul_right, tsum_geometric_of_lt_one ha0 ha1]
        ring]
      field_simp [ne_of_gt (sub_pos.mpr ha1)]

/-- A reporter value at the first hit gives the matching Green-mass lower bound. -/
theorem killedGreen_lower
    {a m : ℝ} {q : ℕ → ℝ} {c : ℕ}
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hq0 : ∀ l, 0 ≤ q l) (hq1 : ∀ l, q l ≤ 1)
    (hhit : (m ^ c)⁻¹ ≤ q c) :
    (1 - a) * (a / m) ^ c ≤ killedGreen a q := by
  have hsum := summable_weighted_of_unit_bound ha0 ha1 hq0 hq1
  have hsingle : a ^ c * q c ≤ ∑' l : ℕ, a ^ l * q l := by
    exact hsum.le_tsum c fun l _ => mul_nonneg (pow_nonneg ha0 _) (hq0 l)
  have hterm : a ^ c * (m ^ c)⁻¹ ≤ a ^ c * q c :=
    mul_le_mul_of_nonneg_left hhit (pow_nonneg ha0 c)
  have hone : 0 ≤ 1 - a := sub_nonneg.mpr ha1.le
  rw [killedGreen, div_pow, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left (hterm.trans hsingle) hone

/-- Abstract first-hit Green sandwich. -/
theorem killedGreen_sandwich
    {a m : ℝ} {q : ℕ → ℝ} {c : ℕ}
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hq0 : ∀ l, 0 ≤ q l) (hq1 : ∀ l, q l ≤ 1)
    (hbefore : ∀ l < c, q l = 0) (hhit : (m ^ c)⁻¹ ≤ q c) :
    (1 - a) * (a / m) ^ c ≤ killedGreen a q ∧ killedGreen a q ≤ a ^ c :=
  ⟨killedGreen_lower ha0 ha1 hq0 hq1 hhit,
    killedGreen_upper ha0 ha1 hq0 hq1 hbefore⟩

section GateWords

variable {X : Type*} [MetricSpace X] {Γ : Type*} [Fintype Γ]

/-- Uniform fraction of length-`l` gate words that reach the target ball. -/
noncomputable def gateHitFraction (act : Γ → X → X) (chi : X) (eps : ℝ) (x : X)
    (l : ℕ) : ℝ := by
  classical
  exact ((Finset.univ.filter fun w : Fin l → Γ =>
    dist x (wordAct act (List.ofFn w) chi) ≤ eps).card : ℝ) /
      (Fintype.card Γ : ℝ) ^ l

theorem gateHitFraction_nonneg (act : Γ → X → X) (chi : X) (eps : ℝ) (x : X)
    (l : ℕ) : 0 ≤ gateHitFraction act chi eps x l := by
  classical
  unfold gateHitFraction
  positivity

theorem gateHitFraction_le_one [Nonempty Γ]
    (act : Γ → X → X) (chi : X) (eps : ℝ) (x : X) (l : ℕ) :
    gateHitFraction act chi eps x l ≤ 1 := by
  classical
  have hcardNat :
      (Finset.univ.filter fun w : Fin l → Γ =>
        dist x (wordAct act (List.ofFn w) chi) ≤ eps).card ≤ Fintype.card Γ ^ l := by
    simpa using
      (Finset.card_filter_le (s := (Finset.univ : Finset (Fin l → Γ)))
        (p := fun w : Fin l → Γ => dist x (wordAct act (List.ofFn w) chi) ≤ eps))
  unfold gateHitFraction
  rw [div_le_one (by positivity : 0 < (Fintype.card Γ : ℝ) ^ l)]
  exact_mod_cast hcardNat

/-- No length below approximate complexity can contribute hit mass. -/
theorem gateHitFraction_eq_zero_of_lt_approxComplexity
    (act : Γ → X → X) (chi : X) (eps : ℝ) (x : X) {l : ℕ}
    (hl : l < approxComplexity act chi eps x) :
    gateHitFraction act chi eps x l = 0 := by
  classical
  have hempty :
      (Finset.univ.filter fun w : Fin l → Γ =>
        dist x (wordAct act (List.ofFn w) chi) ≤ eps) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro w _ hdist
    have hmem : l ∈ {s | ∃ w : List Γ, w.length ≤ s ∧
        dist x (wordAct act w chi) ≤ eps} := ⟨List.ofFn w, by simp, hdist⟩
    exact (not_le.mpr hl) (Nat.sInf_le hmem)
  unfold gateHitFraction
  rw [hempty]
  simp

/-- At least one of the `M ^ c` length-`c` words hits at the minimal complexity. -/
theorem one_div_card_pow_le_gateHitFraction_at_complexity [Nonempty Γ]
    (act : Γ → X → X) (chi : X) (eps : ℝ) (x : X)
    (hS : {s | ∃ w : List Γ, w.length ≤ s ∧
      dist x (wordAct act w chi) ≤ eps}.Nonempty) :
    ((Fintype.card Γ : ℝ) ^ approxComplexity act chi eps x)⁻¹ ≤
      gateHitFraction act chi eps x (approxComplexity act chi eps x) := by
  classical
  set c := approxComplexity act chi eps x with hc
  have hcmem : c ∈ {s | ∃ w : List Γ, w.length ≤ s ∧
      dist x (wordAct act w chi) ≤ eps} := by
    rw [hc]
    exact Nat.sInf_mem hS
  obtain ⟨w, hwlen, hdist⟩ := hcmem
  have hc_le : c ≤ w.length := Nat.sInf_le ⟨w, le_rfl, hdist⟩
  have hlen : w.length = c := Nat.le_antisymm hwlen hc_le
  have hfilter_nonempty :
      (Finset.univ.filter fun u : Fin c → Γ =>
        dist x (wordAct act (List.ofFn u) chi) ≤ eps).Nonempty := by
    let u : Fin c → Γ := fun i => w.get ⟨i.1, by simp [hlen]⟩
    have hu : List.ofFn u = w := by
      apply List.ext_get
      · simp [hlen]
      · intro n h₁ h₂
        simp [u]
    refine ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rw [hu]
    exact hdist
  have hcard : (1 : ℝ) ≤
      ((Finset.univ.filter fun u : Fin c → Γ =>
        dist x (wordAct act (List.ofFn u) chi) ≤ eps).card : ℝ) := by
    exact_mod_cast Finset.one_le_card.mpr hfilter_nonempty
  unfold gateHitFraction
  rw [inv_eq_one_div]
  exact div_le_div_of_nonneg_right hcard (by positivity)

/-- Exact Green sandwich instantiated by finite gate words and `approxComplexity`. -/
theorem gateWalkGreen_sandwich [Nonempty Γ]
    (act : Γ → X → X) (chi : X) (eps : ℝ) (x : X)
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hS : {s | ∃ w : List Γ, w.length ≤ s ∧
      dist x (wordAct act w chi) ≤ eps}.Nonempty) :
    (1 - a) * (a / Fintype.card Γ) ^ approxComplexity act chi eps x ≤
      killedGreen a (gateHitFraction act chi eps x) ∧
    killedGreen a (gateHitFraction act chi eps x) ≤
      a ^ approxComplexity act chi eps x := by
  apply killedGreen_sandwich ha0 ha1
  · exact gateHitFraction_nonneg act chi eps x
  · exact gateHitFraction_le_one act chi eps x
  · intro l hl
    exact gateHitFraction_eq_zero_of_lt_approxComplexity act chi eps x hl
  · exact one_div_card_pow_le_gateHitFraction_at_complexity act chi eps x hS

end GateWords

end HTGeometry
