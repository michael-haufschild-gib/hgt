import GaloisForLFunctions.InfiniteRankPurityTheory.OnTheFlowTheWeightFiltrationNeedsNoChainCondition
import GaloisForLFunctions.HTGeometry.BochnerPositiveDefiniteReal
import GaloisForLFunctions.RHTower.XiWardGlobalCapAndFiniteHeadArithmetic

/-!
# On the flow Castelnuovo–Severi is purity and effectivity

For a curve over a finite field the graphs of the powers of the Frobenius meet in
`Γ_m · Γ_n = q^n (1 + q^{m−n} − t(m − n))`, the degree times a Lefschetz number, and the
Castelnuovo–Severi inequality `D · D ≤ 2 d₁ d₂` on the divisors `D = Σ c_k Γ_{n_k}` is the purity of
the module. This module proves the statement for Frobenius modules of infinite rank on the flow.

Throughout, the module has summable weights `b_i`, modes `ρ_i` in a vertical strip, and finitely
many modes in every disc. Its trace is defined on the whole flow `x > 0`; in the central
normalization it is `φ(u) = Σ b_i e^{u(ρ_i − ½)} = e^{−u/2} t(e^u)` (`centralTrace`,
`frobTrace_exp`).

**The trace determines the module** (`mergedWeight_eq_of_frobTrace_eq_on_flow`). Two such modules
with the same trace on `x ≥ 1` carry the same total weight at every point of the plane; no chain
condition on the weights enters.

**The two involutions on the trace** (`centralTrace_neg_iff`, `conj_centralTrace_iff`,
`graphPairing_comm_iff`). The functional equation `t(1/x) = t(x)/x`, which is `φ(−u) = φ(u)`, holds
exactly when the module is self-dual, `m(1 − w) = m(w)`; equivalently when the intersection pairing
of the Frobenius graphs is symmetric. The trace is real exactly when the module is fixed by the
archimedean involution, `conj m(w̄) = m(w)`.

**Castelnuovo–Severi** (`castelnuovoSeveri_defect`, `positiveDefinite_centralTrace_iff`,
`castelnuovoSeveri_iff`). With `Γ_u · Γ_v = e^v (1 + e^{u−v} − t(e^{u−v}))` the defect
`2 Re(d̄₁ d₂) − D · D` of the divisor `D = Σ c_k Γ_{u_k}` is the quadratic form of `φ` at the
coefficients `c_k e^{u_k/2}`. It is nonnegative for every divisor exactly when every visible mode
lies on the critical line and every merged weight is a nonnegative real: the module is pure and
effective. Purity comes from the bound `‖φ‖ ≤ φ(0)` and the growth filtration on the flow, applied
to the module and to its dual; effectivity from Fejér means along a progression of step `h`, which
read the weight at a mode together with its aliases, and `h → 0`.

**The zero motive** (`zeroMotive_castelnuovoSeveri_iff`). With the lag weights `1/(ρ(1−ρ))` the
inequality on the flow is the Riemann hypothesis.
-/

open Filter Topology
open scoped ComplexConjugate

namespace GaloisForLFunctions.InfiniteRankPurityTheory

open HTGeometry (PositiveDefiniteOnReal geometricAverage geometricAverage_one
  geometricAverage_tendsto_zero norm_geometricAverage_le_one)

variable {ι : Type*} {κ : Type*}

/-! ### Merged weights over the plane -/

/-- The weights at one mode are summable. -/
theorem summable_fiber_of_summable {b ρ : ι → ℂ} (hb : Summable fun i => ‖b i‖) (w : ℂ) :
    Summable fun i => if ρ i = w then b i else 0 := by
  refine Summable.of_norm_bounded hb fun i => ?_
  split_ifs
  · exact le_rfl
  · rw [norm_zero]
    exact norm_nonneg _

theorem mergedWeight_eq_tsum_preimage (b ρ : ι → ℂ) (w : ℂ) :
    mergedWeight b ρ w = ∑' i : ρ ⁻¹' {w}, b i := by
  classical
  rw [mergedWeight, tsum_subtype (ρ ⁻¹' {w}) b]
  refine tsum_congr fun i => ?_
  rw [Set.indicator_apply]
  by_cases h : ρ i = w
  · rw [if_pos h, if_pos (show i ∈ ρ ⁻¹' {w} from h)]
  · rw [if_neg h, if_neg (show i ∉ ρ ⁻¹' {w} from h)]

/-- The merged weights are summable over the plane. -/
theorem summable_norm_mergedWeight_plane {b ρ : ι → ℂ} (hb : Summable fun i => ‖b i‖) :
    Summable fun w : ℂ => ‖mergedWeight b ρ w‖ := by
  have hfib := hb.hasSum.tsum_fiberwise ρ
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun w => ?_) hfib.summable
  rw [mergedWeight_eq_tsum_preimage]
  exact norm_tsum_le_tsum_norm (hb.subtype _)

/-- A sum over the modes is the sum over the points of the plane against the merged weights. -/
theorem hasSum_mergedWeight_mul {b ρ : ι → ℂ} (g : ℂ → ℂ)
    (h : Summable fun i => b i * g (ρ i)) :
    HasSum (fun w : ℂ => mergedWeight b ρ w * g w) (∑' i, b i * g (ρ i)) := by
  have hfib := h.hasSum.tsum_fiberwise ρ
  have hinner : ∀ w : ℂ, (∑' i : ρ ⁻¹' {w}, b i * g (ρ i)) = mergedWeight b ρ w * g w := by
    intro w
    rw [mergedWeight_eq_tsum_preimage, ← tsum_mul_right]
    exact tsum_congr fun i => by rw [show ρ i = w from i.2]
  simpa only [hinner] using hfib

theorem mergedWeight_reflect (b ρ : ι → ℂ) (w : ℂ) :
    mergedWeight b (fun i => 1 - ρ i) w = mergedWeight b ρ (1 - w) := by
  rw [mergedWeight, mergedWeight]
  refine tsum_congr fun i => ?_
  have hiff : (1 - ρ i = w) ↔ ρ i = 1 - w := by
    constructor <;> intro h <;> linear_combination -h
  by_cases h : ρ i = 1 - w
  · rw [if_pos h, if_pos (hiff.mpr h)]
  · rw [if_neg h, if_neg fun h' => h (hiff.mp h')]

theorem mergedWeight_conj (b ρ : ι → ℂ) (w : ℂ) :
    mergedWeight (fun i => conj (b i)) (fun i => conj (ρ i)) w =
      conj (mergedWeight b ρ (conj w)) := by
  rw [mergedWeight, mergedWeight, Complex.conj_tsum]
  refine tsum_congr fun i => ?_
  have hiff : conj (ρ i) = w ↔ ρ i = conj w := by
    constructor
    · intro h
      rw [← h, Complex.conj_conj]
    · intro h
      rw [h, Complex.conj_conj]
  by_cases h : ρ i = conj w
  · rw [if_pos h, if_pos (hiff.mpr h)]
  · rw [if_neg h, if_neg fun h' => h (hiff.mp h'), map_zero]

/-- The reflected module is locally finite. -/
theorem finite_reflect {ρ : ι → ℂ} (hfin : ∀ B : ℝ, {i | ‖ρ i‖ ≤ B}.Finite) (B : ℝ) :
    {i | ‖1 - ρ i‖ ≤ B}.Finite := by
  refine (hfin (B + 1)).subset fun i hi => ?_
  have h1 : ‖ρ i‖ ≤ ‖(1 : ℂ)‖ + ‖1 - ρ i‖ := by
    have := norm_sub_le (1 : ℂ) (1 - ρ i)
    rwa [sub_sub_cancel] at this
  rw [norm_one] at h1
  have hi' : ‖1 - ρ i‖ ≤ B := hi
  show ‖ρ i‖ ≤ B + 1
  linarith

/-! ### The trace on the two-sided flow -/

/-- The trace on the two-sided flow in the central normalization:
`φ(u) = Σ b_i e^{u(ρ_i − ½)} = e^{−u/2} t(e^u)`. -/
noncomputable def centralTrace (b ρ : ι → ℂ) (u : ℝ) : ℂ :=
  ∑' i, b i * Complex.exp ((u : ℂ) * (ρ i - 1 / 2))

theorem re_mul_sub_half (u : ℝ) (z : ℂ) : ((u : ℂ) * (z - 1 / 2)).re = u * (z.re - 1 / 2) := by
  rw [Complex.re_ofReal_mul, Complex.sub_re]
  norm_num

theorem norm_centralTerm_le {b ρ : ι → ℂ} {a A : ℝ} (ha : ∀ i, a ≤ (ρ i).re)
    (hA : ∀ i, (ρ i).re ≤ A) (u : ℝ) (i : ι) :
    ‖b i * Complex.exp ((u : ℂ) * (ρ i - 1 / 2))‖ ≤
      ‖b i‖ * Real.exp (|u| * (|a - 1 / 2| + |A - 1 / 2|)) := by
  rw [norm_mul, Complex.norm_exp, re_mul_sub_half]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  have h1 : |(ρ i).re - 1 / 2| ≤ |a - 1 / 2| + |A - 1 / 2| := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (a - 1 / 2), abs_nonneg (A - 1 / 2), ha i]
    · linarith [le_abs_self (A - 1 / 2), abs_nonneg (a - 1 / 2), hA i]
  calc u * ((ρ i).re - 1 / 2) ≤ |u * ((ρ i).re - 1 / 2)| := le_abs_self _
    _ = |u| * |(ρ i).re - 1 / 2| := abs_mul _ _
    _ ≤ |u| * (|a - 1 / 2| + |A - 1 / 2|) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)

theorem summable_centralTerm {b ρ : ι → ℂ} (hb : Summable fun i => ‖b i‖) {a A : ℝ}
    (ha : ∀ i, a ≤ (ρ i).re) (hA : ∀ i, (ρ i).re ≤ A) (u : ℝ) :
    Summable fun i => b i * Complex.exp ((u : ℂ) * (ρ i - 1 / 2)) :=
  Summable.of_norm_bounded (hb.mul_right _) (norm_centralTerm_le ha hA u)

/-- The trace depends only on the merged weights. -/
theorem hasSum_centralTrace {b ρ : ι → ℂ} (hb : Summable fun i => ‖b i‖) {a A : ℝ}
    (ha : ∀ i, a ≤ (ρ i).re) (hA : ∀ i, (ρ i).re ≤ A) (u : ℝ) :
    HasSum (fun w : ℂ => mergedWeight b ρ w * Complex.exp ((u : ℂ) * (w - 1 / 2)))
      (centralTrace b ρ u) :=
  hasSum_mergedWeight_mul (fun w => Complex.exp ((u : ℂ) * (w - 1 / 2)))
    (summable_centralTerm hb ha hA u)

theorem ofReal_exp_cpow (u : ℝ) (z : ℂ) :
    ((Real.exp u : ℝ) : ℂ) ^ z = Complex.exp ((u : ℂ) * z) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos u).ne'),
    ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp]

/-- The trace at the Frobenius `e^u` is `e^{u/2} φ(u)`. -/
theorem frobTrace_exp (b ρ : ι → ℂ) (u : ℝ) :
    frobTrace b ρ (Real.exp u) = Complex.exp ((u / 2 : ℝ) : ℂ) * centralTrace b ρ u := by
  rw [frobTrace, centralTrace, ← tsum_mul_left]
  refine tsum_congr fun i => ?_
  rw [ofReal_exp_cpow, mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- A bound for `φ` on `u ≥ 0` is a bound `O(x^{1/2})` for the trace on `x ≥ 1`. -/
theorem norm_frobTrace_le_of_centralTrace_le {b ρ : ι → ℂ} {M : ℝ}
    (hM : ∀ u : ℝ, 0 ≤ u → ‖centralTrace b ρ u‖ ≤ M) {x : ℝ} (hx : 1 ≤ x) :
    ‖frobTrace b ρ x‖ ≤ M * x ^ (1 / 2 : ℝ) := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have h := frobTrace_exp b ρ (Real.log x)
  rw [Real.exp_log hx0] at h
  rw [h, norm_mul, Complex.norm_exp, Complex.ofReal_re, Real.rpow_def_of_pos hx0, mul_comm,
    show Real.log x / 2 = Real.log x * (1 / 2) by ring]
  exact mul_le_mul_of_nonneg_right (hM _ (Real.log_nonneg hx)) (Real.exp_pos _).le

/-- The dual module has the reflected trace. -/
theorem centralTrace_reflect (b ρ : ι → ℂ) (u : ℝ) :
    centralTrace b (fun i => 1 - ρ i) u = centralTrace b ρ (-u) := by
  rw [centralTrace, centralTrace]
  refine tsum_congr fun i => ?_
  congr 2
  push_cast
  ring

/-- The conjugate module has the conjugate trace. -/
theorem centralTrace_conj (b ρ : ι → ℂ) (u : ℝ) :
    centralTrace (fun i => conj (b i)) (fun i => conj (ρ i)) u = conj (centralTrace b ρ u) := by
  have h2 : conj ((1 : ℂ) / 2) = 1 / 2 := by
    rw [show ((1 : ℂ) / 2) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]
  rw [centralTrace, centralTrace, Complex.conj_tsum]
  refine tsum_congr fun i => ?_
  rw [map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, map_sub, h2]

/-! ### The trace determines the module -/

/-- **On the flow the trace determines a locally finite module.** Two modules with summable
weights, weights bounded above and finitely many modes in every disc, whose traces agree on
`x ≥ 1`, carry the same total weight at every point. -/
theorem mergedWeight_eq_of_frobTrace_eq_on_flow {b ρ : ι → ℂ} {c σ : κ → ℂ}
    (hb : Summable fun i => ‖b i‖) (hc : Summable fun j => ‖c j‖) {A : ℝ}
    (hA : ∀ i, (ρ i).re ≤ A) (hB : ∀ j, (σ j).re ≤ A)
    (hfin : ∀ B : ℝ, {i | ‖ρ i‖ ≤ B}.Finite) (hfin' : ∀ B : ℝ, {j | ‖σ j‖ ≤ B}.Finite)
    (h : ∀ x : ℝ, 1 ≤ x → frobTrace b ρ x = frobTrace c σ x) (w : ℂ) :
    mergedWeight b ρ w = mergedWeight c σ w := by
  -- the difference module
  have hdsum : Summable fun t : ι ⊕ κ => ‖Sum.elim b (fun j => -c j) t‖ := by
    refine Summable.sum _ ?_ ?_
    · simpa only [Function.comp_def, Sum.elim_inl] using hb
    · simpa only [Function.comp_def, Sum.elim_inr, norm_neg] using hc
  have hνA : ∀ t : ι ⊕ κ, (Sum.elim ρ σ t).re ≤ A := by
    rintro (i | j)
    exacts [hA i, hB j]
  have hνfin : ∀ B : ℝ, {t : ι ⊕ κ | ‖Sum.elim ρ σ t‖ ≤ B}.Finite := by
    intro B
    refine (((hfin B).image Sum.inl).union ((hfin' B).image Sum.inr)).subset ?_
    rintro (i | j) ht
    · exact Or.inl ⟨i, ht, rfl⟩
    · exact Or.inr ⟨j, ht, rfl⟩
  have hzero : ∀ x : ℝ, 1 ≤ x →
      frobTrace (Sum.elim b fun j => -c j) (Sum.elim ρ σ) x = 0 := by
    intro x hx
    have s1 := (summable_frobTerm hb hA hx).hasSum
    have s2 := ((summable_frobTerm hc hB hx).neg).hasSum
    have hsum : HasSum (fun t : ι ⊕ κ => Sum.elim b (fun j => -c j) t *
        (x : ℂ) ^ Sum.elim ρ σ t)
        ((∑' i, b i * (x : ℂ) ^ ρ i) + ∑' j, -(c j * (x : ℂ) ^ σ j)) := by
      refine HasSum.sum ?_ ?_
      · simpa only [Function.comp_def, Sum.elim_inl] using s1
      · simpa only [Function.comp_def, Sum.elim_inr, neg_mul] using s2
    have heq := h x hx
    rw [frobTrace, frobTrace] at heq
    rw [frobTrace, hsum.tsum_eq, tsum_neg, heq]
    ring
  -- its weight at `w` vanishes
  have hm : (∑' t : ι ⊕ κ, if Sum.elim ρ σ t = w then Sum.elim b (fun j => -c j) t else 0) = 0 := by
    by_cases hw : ∃ t : ι ⊕ κ, Sum.elim ρ σ t = w
    · obtain ⟨t, rfl⟩ := hw
      exact mergedWeight_eq_zero_of_flow_bound hdsum hνA hνfin (C := 0)
        (s := (Sum.elim ρ σ t).re - 1) (fun x hx => by rw [hzero x hx]; simp) (by linarith)
    · exact (tsum_congr fun t => if_neg fun h' => hw ⟨t, h'⟩).trans tsum_zero
  -- the weight of the difference module is the difference of the weights
  have hs : HasSum (fun t : ι ⊕ κ => if Sum.elim ρ σ t = w then
      Sum.elim b (fun j => -c j) t else 0)
      ((∑' i, if ρ i = w then b i else 0) + ∑' j, -(if σ j = w then c j else 0)) := by
    refine HasSum.sum ?_ ?_
    · have hfun : ((fun t : ι ⊕ κ => if Sum.elim ρ σ t = w then
          Sum.elim b (fun j => -c j) t else 0) ∘ Sum.inl) = fun i => if ρ i = w then b i else 0 := by
        funext i
        simp only [Function.comp_apply, Sum.elim_inl]
      rw [hfun]
      exact (summable_fiber_of_summable hb w).hasSum
    · have hfun : ((fun t : ι ⊕ κ => if Sum.elim ρ σ t = w then
          Sum.elim b (fun j => -c j) t else 0) ∘ Sum.inr) =
          fun j => -(if σ j = w then c j else 0) := by
        funext j
        simp only [Function.comp_apply, Sum.elim_inr]
        split_ifs <;> simp
      rw [hfun]
      exact ((summable_fiber_of_summable hc w).neg).hasSum
  rw [hs.tsum_eq, tsum_neg] at hm
  exact add_neg_eq_zero.mp hm

/-- The same in the central normalization. -/
theorem mergedWeight_eq_of_centralTrace_eq {b ρ : ι → ℂ} {c σ : κ → ℂ}
    (hb : Summable fun i => ‖b i‖) (hc : Summable fun j => ‖c j‖) {A : ℝ}
    (hA : ∀ i, (ρ i).re ≤ A) (hB : ∀ j, (σ j).re ≤ A)
    (hfin : ∀ B : ℝ, {i | ‖ρ i‖ ≤ B}.Finite) (hfin' : ∀ B : ℝ, {j | ‖σ j‖ ≤ B}.Finite)
    (h : ∀ u : ℝ, 0 ≤ u → centralTrace b ρ u = centralTrace c σ u) (w : ℂ) :
    mergedWeight b ρ w = mergedWeight c σ w := by
  refine mergedWeight_eq_of_frobTrace_eq_on_flow hb hc hA hB hfin hfin' (fun x hx => ?_) w
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have h1 := frobTrace_exp b ρ (Real.log x)
  have h2 := frobTrace_exp c σ (Real.log x)
  rw [Real.exp_log hx0] at h1 h2
  rw [h1, h2, h _ (Real.log_nonneg hx)]

/-! ### The two involutions on the trace -/

/-- **The functional equation of the trace is the duality of the module.** `φ(−u) = φ(u)`, that
is `t(1/x) = t(x)/x`, exactly when `m(1 − w) = m(w)` at every point. -/
theorem centralTrace_neg_iff {b ρ : ι → ℂ} (hb : Summable fun i => ‖b i‖) {a A : ℝ}
    (ha : ∀ i, a ≤ (ρ i).re) (hA : ∀ i, (ρ i).re ≤ A)
    (hfin : ∀ B : ℝ, {i | ‖ρ i‖ ≤ B}.Finite) :
    (∀ u : ℝ, centralTrace b ρ (-u) = centralTrace b ρ u) ↔
      ∀ w : ℂ, mergedWeight b ρ (1 - w) = mergedWeight b ρ w := by
  have ha' : ∀ i, 1 - A ≤ (1 - ρ i).re := fun i => by
    rw [Complex.sub_re, Complex.one_re]
    linarith [hA i]
  have hA' : ∀ i, (1 - ρ i).re ≤ 1 - a := fun i => by
    rw [Complex.sub_re, Complex.one_re]
    linarith [ha i]
  constructor
  · intro h w
    rw [← mergedWeight_reflect]
    refine mergedWeight_eq_of_centralTrace_eq hb hb (A := max A (1 - a))
      (fun i => (hA' i).trans (le_max_right _ _)) (fun i => (hA i).trans (le_max_left _ _))
      (finite_reflect hfin) hfin (fun u _ => ?_) w
    rw [centralTrace_reflect, h]
  · intro h u
    rw [← centralTrace_reflect, ← (hasSum_centralTrace hb ha' hA' u).tsum_eq,
      ← (hasSum_centralTrace hb ha hA u).tsum_eq]
    exact tsum_congr fun w => by rw [mergedWeight_reflect, h]

/-- **The trace is real exactly when the module is fixed by the archimedean involution.** -/
theorem conj_centralTrace_iff {b ρ : ι → ℂ} (hb : Summable fun i => ‖b i‖) {a A : ℝ}
    (ha : ∀ i, a ≤ (ρ i).re) (hA : ∀ i, (ρ i).re ≤ A)
    (hfin : ∀ B : ℝ, {i | ‖ρ i‖ ≤ B}.Finite) :
    (∀ u : ℝ, conj (centralTrace b ρ u) = centralTrace b ρ u) ↔
      ∀ w : ℂ, conj (mergedWeight b ρ (conj w)) = mergedWeight b ρ w := by
  have hb' : Summable fun i => ‖conj (b i)‖ := by simpa only [Complex.norm_conj] using hb
  have ha' : ∀ i, a ≤ (conj (ρ i)).re := fun i => by rw [Complex.conj_re]; exact ha i
  have hA' : ∀ i, (conj (ρ i)).re ≤ A := fun i => by rw [Complex.conj_re]; exact hA i
  have hfin' : ∀ B : ℝ, {i | ‖conj (ρ i)‖ ≤ B}.Finite := fun B => by
    simpa only [Complex.norm_conj] using hfin B
  constructor
  · intro h w
    rw [← mergedWeight_conj]
    refine mergedWeight_eq_of_centralTrace_eq hb' hb hA' hA hfin' hfin (fun u _ => ?_) w
    rw [centralTrace_conj, h]
  · intro h u
    rw [← centralTrace_conj, ← (hasSum_centralTrace hb' ha' hA' u).tsum_eq,
      ← (hasSum_centralTrace hb ha hA u).tsum_eq]
    exact tsum_congr fun w => by rw [mergedWeight_conj, h]

/-! ### The quadratic form of the trace -/

/-- For a module whose visible modes lie on the critical line the quadratic form of `φ` is the sum
over the modes of the weight times the squared modulus of the exponential sum. -/
theorem hasSum_quadraticForm {b ρ : ι → ℂ} (hb : Summable fun i => ‖b i‖) {a A : ℝ}
    (ha : ∀ i, a ≤ (ρ i).re) (hA : ∀ i, (ρ i).re ≤ A)
    (hpure : ∀ w : ℂ, mergedWeight b ρ w ≠ 0 → w.re = 1 / 2) {N : ℕ} (t : Fin N → ℝ)
    (c : Fin N → ℂ) :
    HasSum (fun w : ℂ => mergedWeight b ρ w *
        ((Complex.normSq (∑ j, c j * Complex.exp ((t j : ℂ) * (w - 1 / 2))) : ℝ) : ℂ))
      (∑ i, ∑ j, star (c i) * centralTrace b ρ (t j - t i) * c j) := by
  have hterm : ∀ i j : Fin N, HasSum (fun w : ℂ => star (c i) *
      (mergedWeight b ρ w * Complex.exp (((t j - t i : ℝ) : ℂ) * (w - 1 / 2))) * c j)
      (star (c i) * centralTrace b ρ (t j - t i) * c j) := fun i j =>
    ((hasSum_centralTrace hb ha hA (t j - t i)).mul_left _).mul_right _
  have hsum := hasSum_sum (s := Finset.univ) fun i (_ : i ∈ Finset.univ) =>
    hasSum_sum (s := Finset.univ) fun j (_ : j ∈ Finset.univ) => hterm i j
  have hfun : (fun w : ℂ => mergedWeight b ρ w *
      ((Complex.normSq (∑ j, c j * Complex.exp ((t j : ℂ) * (w - 1 / 2))) : ℝ) : ℂ)) =
      fun w : ℂ => ∑ i, ∑ j, star (c i) *
        (mergedWeight b ρ w * Complex.exp (((t j - t i : ℝ) : ℂ) * (w - 1 / 2))) * c j := by
    funext w
    by_cases hm : mergedWeight b ρ w = 0
    · simp only [hm, zero_mul, mul_zero, Finset.sum_const_zero]
    · have hre := hpure w hm
      -- on the critical line `w − ½` is purely imaginary
      have hcw : conj (w - 1 / 2) = -(w - 1 / 2) := by
        apply Complex.ext
        · rw [Complex.conj_re, Complex.neg_re, Complex.sub_re, hre]
          norm_num
        · rw [Complex.conj_im, Complex.neg_im]
      have hE : ∀ i j : Fin N, Complex.exp (((t j - t i : ℝ) : ℂ) * (w - 1 / 2)) =
          conj (Complex.exp ((t i : ℂ) * (w - 1 / 2))) *
            Complex.exp ((t j : ℂ) * (w - 1 / 2)) := by
        intro i j
        rw [← Complex.exp_conj, ← Complex.exp_add, map_mul, Complex.conj_ofReal, hcw]
        congr 1
        push_cast
        ring
      rw [Complex.normSq_eq_conj_mul_self, map_sum, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hE, map_mul, Complex.star_def]
      ring
  rw [hfun]
  exact hsum

/-- A pure and effective module has a positive definite trace. -/
theorem positiveDefinite_centralTrace_of_pure_of_effective {b ρ : ι → ℂ}
    (hb : Summable fun i => ‖b i‖) {a A : ℝ} (ha : ∀ i, a ≤ (ρ i).re) (hA : ∀ i, (ρ i).re ≤ A)
    (hpure : ∀ w : ℂ, mergedWeight b ρ w ≠ 0 → w.re = 1 / 2)
    (heff : ∀ w : ℂ, (mergedWeight b ρ w).im = 0 ∧ 0 ≤ (mergedWeight b ρ w).re) :
    PositiveDefiniteOnReal (centralTrace b ρ) := by
  intro N t c
  have h := hasSum_quadraticForm hb ha hA hpure t c
  refine ⟨∑' w : ℂ, (mergedWeight b ρ w).re *
      Complex.normSq (∑ j, c j * Complex.exp ((t j : ℂ) * (w - 1 / 2))),
    tsum_nonneg fun w => mul_nonneg (heff w).2 (Complex.normSq_nonneg _), ?_⟩
  rw [Complex.ofReal_tsum, ← h.tsum_eq]
  refine tsum_congr fun w => ?_
  rw [Complex.ofReal_mul]
  congr 1
  exact Complex.ext (Complex.ofReal_re _).symm (by rw [Complex.ofReal_im]; exact (heff w).1)

/-- **A positive definite trace is pure.** The bound `‖φ‖ ≤ φ(0)` is a bound `O(x^{1/2})` for the
traces of the module and of its dual on the flow, and the growth filtration excludes every visible
mode on either side of the critical line. -/
theorem re_eq_half_of_positiveDefinite {b ρ : ι → ℂ} (hb : Summable fun i => ‖b i‖) {a A : ℝ}
    (ha : ∀ i, a ≤ (ρ i).re) (hA : ∀ i, (ρ i).re ≤ A)
    (hfin : ∀ B : ℝ, {i | ‖ρ i‖ ≤ B}.Finite)
    (hpd : PositiveDefiniteOnReal (centralTrace b ρ)) {w : ℂ} (hw : mergedWeight b ρ w ≠ 0) :
    w.re = 1 / 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, ρ j = w := by
    by_contra hne
    exact hw ((tsum_congr fun i => if_neg fun h => hne ⟨i, h⟩).trans tsum_zero)
  have hA' : ∀ i, (1 - ρ i).re ≤ 1 - a := fun i => by
    rw [Complex.sub_re, Complex.one_re]
    linarith [ha i]
  refine le_antisymm (not_lt.mp fun hlt => hw ?_) (not_lt.mp fun hlt => hw ?_)
  · exact mergedWeight_eq_zero_of_flow_bound hb hA hfin
      (fun x hx => norm_frobTrace_le_of_centralTrace_le (fun u _ => hpd.norm_le u) hx) hlt
  · have hj : (1 / 2 : ℝ) < (1 - ρ j).re := by
      rw [Complex.sub_re, Complex.one_re]
      linarith
    have h := mergedWeight_eq_zero_of_flow_bound hb hA' (finite_reflect hfin)
      (fun x hx => norm_frobTrace_le_of_centralTrace_le
        (fun u _ => by rw [centralTrace_reflect]; exact hpd.norm_le (-u)) hx) hj
    have h' : mergedWeight b (fun i => 1 - ρ i) (1 - ρ j) = 0 := h
    rwa [mergedWeight_reflect, sub_sub_cancel] at h'

/-- A limit of nonnegative reals is a nonnegative real. -/
theorem im_eq_zero_and_re_nonneg_of_tendsto {x : ℕ → ℂ} {L : ℂ} (hx : Tendsto x atTop (𝓝 L))
    (h : ∀ n, (x n).im = 0 ∧ 0 ≤ (x n).re) : L.im = 0 ∧ 0 ≤ L.re := by
  refine ⟨?_, ?_⟩
  · have him : Tendsto (fun n => (x n).im) atTop (𝓝 L.im) :=
      (Complex.continuous_im.tendsto L).comp hx
    exact tendsto_nhds_unique him (tendsto_const_nhds.congr fun n => ((h n).1).symm)
  · have hre : Tendsto (fun n => (x n).re) atTop (𝓝 L.re) :=
      (Complex.continuous_re.tendsto L).comp hx
    exact ge_of_tendsto' hre fun n => (h n).2

/-- A small step separates a mode from its aliases. -/
theorem exp_mul_ne_one {z : ℂ} (hz : z ≠ 0) {h : ℝ} (hh : 0 < h)
    (hsmall : h * ‖z‖ < 2 * Real.pi) : Complex.exp ((h : ℂ) * z) ≠ 1 := by
  intro h1
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
  have h2pi : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
    rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le, mul_one, Complex.norm_ofNat]
  have hnorm : h * ‖z‖ = |(n : ℝ)| * (2 * Real.pi) := by
    have := congrArg norm hn
    rwa [norm_mul, Complex.norm_real, Real.norm_of_nonneg hh.le, norm_mul,
      Complex.norm_intCast, h2pi] at this
  rcases eq_or_ne n 0 with rfl | hn0
  · rw [Int.cast_zero, abs_zero, zero_mul] at hnorm
    rcases mul_eq_zero.mp hnorm with h0 | h0
    · exact hh.ne' h0
    · exact hz (norm_eq_zero.mp h0)
  · have h1' : (1 : ℝ) ≤ |(n : ℝ)| := by
      have := Int.one_le_abs hn0
      exact_mod_cast this
    have := mul_le_mul_of_nonneg_right h1' (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    linarith

theorem norm_exp_step {w w₀ : ℂ} (h : ℝ) (hw : w.re = 1 / 2) (hw₀ : w₀.re = 1 / 2) :
    ‖Complex.exp ((h : ℂ) * (w - w₀))‖ = 1 := by
  rw [Complex.norm_exp, Complex.re_ofReal_mul, Complex.sub_re, hw, hw₀, sub_self, mul_zero,
    Real.exp_zero]

/-- The exponential sum of the Fejér coefficients along a progression of step `h` is a geometric
average. -/
theorem fejer_expSum (h : ℝ) (N : ℕ) (w w₀ : ℂ) :
    (∑ k : Fin (N + 1), (((N + 1 : ℕ) : ℂ)⁻¹ *
        Complex.exp (-(((k : ℕ) * h : ℝ) : ℂ) * (w₀ - 1 / 2))) *
      Complex.exp ((((k : ℕ) * h : ℝ) : ℂ) * (w - 1 / 2))) =
      geometricAverage (Complex.exp ((h : ℂ) * (w - w₀))) N := by
  rw [geometricAverage, Finset.mul_sum, ← Fin.sum_univ_eq_sum_range
    (fun k => ((N + 1 : ℕ) : ℂ)⁻¹ * Complex.exp ((h : ℂ) * (w - w₀)) ^ k) (N + 1)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_assoc, ← Complex.exp_add, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

/-- **A positive definite trace is effective.** Along the progression of step `h` the Fejér means
of the quadratic form tend to the weight carried at `w₀` and at its aliases
`w₀ + 2πik/h`; as `h → 0` the aliases leave every disc. -/
theorem effective_of_positiveDefinite {b ρ : ι → ℂ} (hb : Summable fun i => ‖b i‖) {a A : ℝ}
    (ha : ∀ i, a ≤ (ρ i).re) (hA : ∀ i, (ρ i).re ≤ A)
    (hpure : ∀ w : ℂ, mergedWeight b ρ w ≠ 0 → w.re = 1 / 2)
    (hpd : PositiveDefiniteOnReal (centralTrace b ρ)) (w₀ : ℂ) :
    (mergedWeight b ρ w₀).im = 0 ∧ 0 ≤ (mergedWeight b ρ w₀).re := by
  by_cases hm0 : mergedWeight b ρ w₀ = 0
  · rw [hm0]
    exact ⟨Complex.zero_im, le_of_eq Complex.zero_re.symm⟩
  have hre0 := hpure w₀ hm0
  have hmsum := summable_norm_mergedWeight_plane (ρ := ρ) hb
  -- the Fejér means are nonnegative reals
  have hq : ∀ (h : ℝ) (N : ℕ),
      (∑' w : ℂ, mergedWeight b ρ w * ((Complex.normSq
        (geometricAverage (Complex.exp ((h : ℂ) * (w - w₀))) N) : ℝ) : ℂ)).im = 0 ∧
      0 ≤ (∑' w : ℂ, mergedWeight b ρ w * ((Complex.normSq
        (geometricAverage (Complex.exp ((h : ℂ) * (w - w₀))) N) : ℝ) : ℂ)).re := by
    intro h N
    have hs := hasSum_quadraticForm hb ha hA hpure (fun k : Fin (N + 1) => (k : ℕ) * h)
      (fun k : Fin (N + 1) => ((N + 1 : ℕ) : ℂ)⁻¹ *
        Complex.exp (-(((k : ℕ) * h : ℝ) : ℂ) * (w₀ - 1 / 2)))
    have hpos := hpd.re_nonneg_im_eq_zero (fun k : Fin (N + 1) => (k : ℕ) * h)
      (fun k : Fin (N + 1) => ((N + 1 : ℕ) : ℂ)⁻¹ *
        Complex.exp (-(((k : ℕ) * h : ℝ) : ℂ) * (w₀ - 1 / 2)))
    rw [← hs.tsum_eq] at hpos
    simp only [fejer_expSum] at hpos
    exact ⟨hpos.2, hpos.1⟩
  -- the limit `N → ∞` at a fixed step
  have hlimN : ∀ h : ℝ, Tendsto (fun N : ℕ => ∑' w : ℂ, mergedWeight b ρ w *
      ((Complex.normSq (geometricAverage (Complex.exp ((h : ℂ) * (w - w₀))) N) : ℝ) : ℂ)) atTop
      (𝓝 (∑' w : ℂ, if Complex.exp ((h : ℂ) * (w - w₀)) = 1 then mergedWeight b ρ w else 0)) := by
    intro h
    refine tendsto_tsum_of_dominated_convergence hmsum (fun w => ?_)
      (Eventually.of_forall fun N w => ?_)
    · by_cases hm : mergedWeight b ρ w = 0
      · simp only [hm, zero_mul, ite_self]
        exact tendsto_const_nhds
      · have hz := norm_exp_step h (hpure w hm) hre0
        by_cases hz1 : Complex.exp ((h : ℂ) * (w - w₀)) = 1
        · simp only [hz1, geometricAverage_one, map_one, Complex.ofReal_one, mul_one, if_true]
          exact tendsto_const_nhds
        · rw [if_neg hz1]
          have h2 : Tendsto (fun N : ℕ => ((Complex.normSq
              (geometricAverage (Complex.exp ((h : ℂ) * (w - w₀))) N) : ℝ) : ℂ)) atTop
              (𝓝 ((Complex.normSq (0 : ℂ) : ℝ) : ℂ)) :=
            ((Complex.continuous_ofReal.comp Complex.continuous_normSq).tendsto 0).comp
              (geometricAverage_tendsto_zero hz hz1)
          rw [map_zero, Complex.ofReal_zero] at h2
          have h3 := h2.const_mul (mergedWeight b ρ w)
          rwa [mul_zero] at h3
    · by_cases hm : mergedWeight b ρ w = 0
      · rw [hm, zero_mul, norm_zero]
      · have hz := norm_exp_step h (hpure w hm) hre0
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Complex.normSq_nonneg _),
          Complex.normSq_eq_norm_sq]
        exact mul_le_of_le_one_right (norm_nonneg _)
          (pow_le_one₀ (norm_nonneg _) (norm_geometricAverage_le_one hz N))
  -- the weight at `w₀` with its aliases is a nonnegative real
  have hA' : ∀ h : ℝ,
      (∑' w : ℂ, if Complex.exp ((h : ℂ) * (w - w₀)) = 1 then mergedWeight b ρ w else 0).im = 0 ∧
      0 ≤ (∑' w : ℂ, if Complex.exp ((h : ℂ) * (w - w₀)) = 1
        then mergedWeight b ρ w else 0).re :=
    fun h => im_eq_zero_and_re_nonneg_of_tendsto (hlimN h) (hq h)
  -- the limit `h → 0`
  have hlimh : Tendsto (fun n : ℕ => ∑' w : ℂ,
      if Complex.exp (((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * (w - w₀)) = 1
        then mergedWeight b ρ w else 0) atTop
      (𝓝 (∑' w : ℂ, if w = w₀ then mergedWeight b ρ w else 0)) := by
    refine tendsto_tsum_of_dominated_convergence hmsum (fun w => ?_)
      (Eventually.of_forall fun n w => ?_)
    · by_cases hw : w = w₀
      · simp only [hw, sub_self, mul_zero, Complex.exp_zero, if_true]
        exact tendsto_const_nhds
      · rw [if_neg hw]
        have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1) * ‖w - w₀‖) atTop (𝓝 0) := by
          simpa using tendsto_one_div_add_atTop_nhds_zero_nat.mul_const ‖w - w₀‖
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [ht.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 2 * Real.pi))]
          with n hn
        exact (if_neg (exp_mul_ne_one (sub_ne_zero.mpr hw) (by positivity) hn)).symm
    · split_ifs
      · exact le_rfl
      · rw [norm_zero]
        exact norm_nonneg _
  rw [tsum_eq_single w₀ (fun w hw => if_neg hw), if_pos rfl] at hlimh
  exact im_eq_zero_and_re_nonneg_of_tendsto hlimh fun n => hA' _

/-- **On the flow a positive trace form is purity and effectivity.** For a locally finite module in
a vertical strip, `φ` is positive definite exactly when every visible mode lies on the critical
line and every merged weight is a nonnegative real. -/
theorem positiveDefinite_centralTrace_iff {b ρ : ι → ℂ} (hb : Summable fun i => ‖b i‖)
    {a A : ℝ} (ha : ∀ i, a ≤ (ρ i).re) (hA : ∀ i, (ρ i).re ≤ A)
    (hfin : ∀ B : ℝ, {i | ‖ρ i‖ ≤ B}.Finite) :
    PositiveDefiniteOnReal (centralTrace b ρ) ↔
      (∀ w : ℂ, mergedWeight b ρ w ≠ 0 → w.re = 1 / 2) ∧
        ∀ w : ℂ, (mergedWeight b ρ w).im = 0 ∧ 0 ≤ (mergedWeight b ρ w).re := by
  constructor
  · intro hpd
    have hpure : ∀ w : ℂ, mergedWeight b ρ w ≠ 0 → w.re = 1 / 2 := fun w hw =>
      re_eq_half_of_positiveDefinite hb ha hA hfin hpd hw
    exact ⟨hpure, effective_of_positiveDefinite hb ha hA hpure hpd⟩
  · rintro ⟨hpure, heff⟩
    exact positiveDefinite_centralTrace_of_pure_of_effective hb ha hA hpure heff

/-! ### Castelnuovo–Severi -/

/-- The intersection number of the graphs of the Frobenii `e^u` and `e^v`: the degree `e^v` times
the Lefschetz number `1 + x − t(x)` of the Frobenius `x = e^{u−v}`. -/
noncomputable def graphPairing (b ρ : ι → ℂ) (u v : ℝ) : ℂ :=
  (Real.exp v : ℂ) * (1 + (Real.exp (u - v) : ℂ) - frobTrace b ρ (Real.exp (u - v)))

theorem graphPairing_eq (b ρ : ι → ℂ) (u v : ℝ) :
    graphPairing b ρ u v = (Real.exp u : ℂ) + (Real.exp v : ℂ) -
      (Real.exp ((u + v) / 2) : ℂ) * centralTrace b ρ (u - v) := by
  have h1 : Real.exp v * Real.exp (u - v) = Real.exp u := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h2 : Real.exp v * Real.exp ((u - v) / 2) = Real.exp ((u + v) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [graphPairing, frobTrace_exp, ← Complex.ofReal_exp, ← h1, ← h2]
  push_cast
  ring

/-- **The pairing of the graphs is symmetric exactly when the module is self-dual.** -/
theorem graphPairing_comm_iff {b ρ : ι → ℂ} (hb : Summable fun i => ‖b i‖) {a A : ℝ}
    (ha : ∀ i, a ≤ (ρ i).re) (hA : ∀ i, (ρ i).re ≤ A)
    (hfin : ∀ B : ℝ, {i | ‖ρ i‖ ≤ B}.Finite) :
    (∀ u v : ℝ, graphPairing b ρ u v = graphPairing b ρ v u) ↔
      ∀ w : ℂ, mergedWeight b ρ (1 - w) = mergedWeight b ρ w := by
  rw [← centralTrace_neg_iff hb ha hA hfin]
  constructor
  · intro h u
    have h0 := h 0 u
    rw [graphPairing_eq, graphPairing_eq, zero_sub, sub_zero, zero_add, add_zero] at h0
    have hne : (Real.exp (u / 2) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
    refine mul_left_cancel₀ hne ?_
    linear_combination -h0
  · intro h u v
    rw [graphPairing_eq, graphPairing_eq, show v - u = -(u - v) by ring, h, add_comm v u]
    ring

/-- **The Castelnuovo–Severi defect is the quadratic form of the trace.** For the divisor
`D = Σ c_k Γ_{t_k}` with degrees `d₁ = Σ c_k`, `d₂ = Σ c_k e^{t_k}`, the defect
`d̄₁ d₂ + d̄₂ d₁ − D · D` is the form of `φ` at the coefficients `c_k e^{t_k/2}`. -/
theorem castelnuovoSeveri_defect (b ρ : ι → ℂ) {N : ℕ} (t : Fin N → ℝ) (c : Fin N → ℂ) :
    conj (∑ i, c i) * (∑ j, c j * (Real.exp (t j) : ℂ)) +
        conj (∑ i, c i * (Real.exp (t i) : ℂ)) * (∑ j, c j) -
        ∑ i, ∑ j, star (c i) * graphPairing b ρ (t j) (t i) * c j =
      ∑ i, ∑ j, star (c i * (Real.exp (t i / 2) : ℂ)) * centralTrace b ρ (t j - t i) *
        (c j * (Real.exp (t j / 2) : ℂ)) := by
  rw [map_sum, map_sum, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hE : (Real.exp ((t j + t i) / 2) : ℂ) =
      (Real.exp (t i / 2) : ℂ) * (Real.exp (t j / 2) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  rw [graphPairing_eq, hE, Complex.star_def, map_mul, map_mul, Complex.conj_ofReal,
    Complex.conj_ofReal]
  ring

/-- The inequality for all divisors of graphs is positive definiteness of the trace. -/
theorem castelnuovoSeveri_iff_positiveDefinite (b ρ : ι → ℂ) :
    (∀ (N : ℕ) (t : Fin N → ℝ) (c : Fin N → ℂ), ∃ r : ℝ, 0 ≤ r ∧
      conj (∑ i, c i) * (∑ j, c j * (Real.exp (t j) : ℂ)) +
        conj (∑ i, c i * (Real.exp (t i) : ℂ)) * (∑ j, c j) -
        ∑ i, ∑ j, star (c i) * graphPairing b ρ (t j) (t i) * c j = (r : ℂ)) ↔
      PositiveDefiniteOnReal (centralTrace b ρ) := by
  constructor
  · intro h N t c
    obtain ⟨r, hr, he⟩ := h N t fun j => c j * (Real.exp (-(t j / 2)) : ℂ)
    refine ⟨r, hr, ?_⟩
    rw [← he, castelnuovoSeveri_defect]
    have hc : ∀ j, c j * (Real.exp (-(t j / 2)) : ℂ) * (Real.exp (t j / 2) : ℂ) = c j := by
      intro j
      rw [mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
        Complex.ofReal_one, mul_one]
    simp only [hc]
  · intro hpd N t c
    obtain ⟨r, hr, he⟩ := hpd N t fun j => c j * (Real.exp (t j / 2) : ℂ)
    exact ⟨r, hr, by rw [castelnuovoSeveri_defect]; exact he⟩

/-- **Castelnuovo–Severi on the flow.** For a locally finite module in a vertical strip the
inequality `D · D ≤ 2 Re(d̄₁ d₂)` holds for every divisor of Frobenius graphs exactly when the
module is pure and effective. -/
theorem castelnuovoSeveri_iff {b ρ : ι → ℂ} (hb : Summable fun i => ‖b i‖) {a A : ℝ}
    (ha : ∀ i, a ≤ (ρ i).re) (hA : ∀ i, (ρ i).re ≤ A)
    (hfin : ∀ B : ℝ, {i | ‖ρ i‖ ≤ B}.Finite) :
    (∀ (N : ℕ) (t : Fin N → ℝ) (c : Fin N → ℂ), ∃ r : ℝ, 0 ≤ r ∧
      conj (∑ i, c i) * (∑ j, c j * (Real.exp (t j) : ℂ)) +
        conj (∑ i, c i * (Real.exp (t i) : ℂ)) * (∑ j, c j) -
        ∑ i, ∑ j, star (c i) * graphPairing b ρ (t j) (t i) * c j = (r : ℂ)) ↔
      (∀ w : ℂ, mergedWeight b ρ w ≠ 0 → w.re = 1 / 2) ∧
        ∀ w : ℂ, (mergedWeight b ρ w).im = 0 ∧ 0 ≤ (mergedWeight b ρ w).re := by
  rw [castelnuovoSeveri_iff_positiveDefinite, positiveDefinite_centralTrace_iff hb ha hA hfin]

/-! ### The zero motive -/

open _root_.RHTower GaloisForLFunctions.BlackHoleRingdown in
open GaloisForLFunctions.InfiniteRankWeilTheory renaming lagWeight → lagW,
  summable_norm_lagWeight → summable_norm_lagW, re_lagWeight_pos → re_lagW_pos in
/-- **For the zero motive Castelnuovo–Severi on the flow is the Riemann hypothesis.** With the lag
weights `1/(ρ(1−ρ))` the zeros form a locally finite module in the strip; every zero is visible, and
on the critical line the weights are positive. -/
theorem zeroMotive_castelnuovoSeveri_iff :
    (∀ (N : ℕ) (t : Fin N → ℝ) (c : Fin N → ℂ), ∃ r : ℝ, 0 ≤ r ∧
      conj (∑ i, c i) * (∑ j, c j * (Real.exp (t j) : ℂ)) +
        conj (∑ i, c i * (Real.exp (t i) : ℂ)) * (∑ j, c j) -
        ∑ i, ∑ j, star (c i) *
          graphPairing lagW (fun q : XiZeroCopy => (q.1 : ℂ)) (t j) (t i) * c j = (r : ℂ)) ↔
      RiemannHypothesis := by
  have ha : ∀ q : XiZeroCopy, (0 : ℝ) ≤ (q.1 : ℂ).re := fun q => (xiZeroCopy_re_pos q).le
  have hA : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 1 := fun q => (xiZeroCopy_re_lt_one q).le
  have hfin : ∀ B : ℝ, {q : XiZeroCopy | ‖(q.1 : ℂ)‖ ≤ B}.Finite := by
    intro B
    refine (finite_xiZeroCopy_band 0 (abs_nonneg B)).subset fun q hq => ?_
    have hq' : ‖(q.1 : ℂ)‖ ≤ B := hq
    show |(q.1 : ℂ).im - 0| ≤ |B|
    rw [sub_zero]
    exact (Complex.abs_im_le_norm _).trans (hq'.trans (le_abs_self B))
  rw [castelnuovoSeveri_iff summable_norm_lagW ha hA hfin,
    riemannHypothesis_iff_forall_xiZeroCopy_re_eq_half]
  constructor
  · rintro ⟨hpure, -⟩ q
    exact hpure _ (merged_ne_zero_of_re_pos summable_norm_lagW (fun q => (re_lagW_pos q).le)
      (re_lagW_pos q))
  · intro hRH
    -- on the critical line `ρ(1 − ρ) = ‖ρ‖²`, so the lag weights are real
    have hreal : ∀ q : XiZeroCopy, (lagW q).im = 0 := by
      intro q
      have hc : (1 : ℂ) - (q.1 : ℂ) = conj (q.1 : ℂ) := by
        apply Complex.ext
        · rw [Complex.sub_re, Complex.one_re, Complex.conj_re, hRH q]
          norm_num
        · rw [Complex.sub_im, Complex.one_im, Complex.conj_im, zero_sub]
      show (1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).im = 0
      rw [hc, Complex.mul_conj, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_im]
    refine ⟨fun w hw => ?_, fun w => ?_⟩
    · obtain ⟨q, rfl⟩ : ∃ q : XiZeroCopy, (q.1 : ℂ) = w := by
        by_contra hne
        exact hw ((tsum_congr fun q => if_neg fun h => hne ⟨q, h⟩).trans tsum_zero)
      exact hRH q
    · have hs := summable_fiber_of_summable (ρ := fun q : XiZeroCopy => (q.1 : ℂ))
        summable_norm_lagW w
      rw [mergedWeight, Complex.im_tsum hs, Complex.re_tsum hs]
      refine ⟨(tsum_congr fun q => ?_).trans tsum_zero, tsum_nonneg fun q => ?_⟩
      · split_ifs
        · exact hreal q
        · exact Complex.zero_im
      · split_ifs
        · exact (re_lagW_pos q).le
        · exact le_of_eq Complex.zero_re.symm

end GaloisForLFunctions.InfiniteRankPurityTheory
