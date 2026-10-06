import Mathlib

/-!
# Shannon entropy and conditional entropy of countably-valued observables

For a measure `μ` on `Ω` and measurable observables `f : Ω → α`, `g : Ω → β` with countable
discrete value sets, the Shannon entropy and the conditional entropy are

`H_μ(f) = ∑_a η(μ{f = a})`,
`H_μ(f | g) = ∑_{a,b} μ{f = a, g = b} log (μ{g = b} / μ{f = a, g = b})`,

with `η(t) = -t log t`, valued in `[0, ∞]`.  Proved here, with infinite values allowed throughout:

* the chain rule `H(f, g | k) = H(g | k) + H(f | g, k)` and `H(f, g) = H(g) + H(f | g)`;
* conditioning reduces entropy, `H(f | g, k) ≤ H(f | g)`, by the countable log-sum inequality;
* invariance under injective relabelling, under measure-preserving maps and under a.e. equality;
* monotonicity under coarsening, `H(f | g) ≤ H(f)`, subadditivity, and additivity for
  independent observables.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry.ObservableEntropy

/-- The Shannon term `η(t) = -t log t` of a mass `t`. -/
def entropyTerm (t : ℝ≥0∞) : ℝ≥0∞ := ENNReal.ofReal (Real.negMulLog t.toReal)

/-- The conditional Shannon term `s log(t/s)` of a joint mass `s` inside a conditioning mass `t`. -/
def condTerm (s t : ℝ≥0∞) : ℝ≥0∞ := ENNReal.ofReal (s.toReal * Real.log (t.toReal / s.toReal))

theorem condTerm_zero_left (t : ℝ≥0∞) : condTerm 0 t = 0 := by simp [condTerm]

theorem condTerm_one_right (s : ℝ≥0∞) : condTerm s 1 = entropyTerm s := by
  rw [condTerm, entropyTerm, ENNReal.toReal_one, one_div, Real.log_inv, Real.negMulLog]
  ring_nf

/-- Splitting a conditional term through an intermediate mass `s ≤ u ≤ t`. -/
theorem condTerm_split {s u t : ℝ≥0∞} (hsu : s ≤ u) (hut : u ≤ t) (ht : t ≠ ⊤) :
    condTerm s t = ENNReal.ofReal (s.toReal * Real.log (t.toReal / u.toReal)) + condTerm s u := by
  by_cases hs : s = 0
  · simp [condTerm, hs]
  have hu' : u ≠ ⊤ := ne_top_of_le_ne_top ht hut
  have hs' : s ≠ ⊤ := ne_top_of_le_ne_top hu' hsu
  have hs0 : 0 < s.toReal := ENNReal.toReal_pos hs hs'
  have hsu' : s.toReal ≤ u.toReal := ENNReal.toReal_mono hu' hsu
  have hut' : u.toReal ≤ t.toReal := ENNReal.toReal_mono ht hut
  have hu0 : 0 < u.toReal := hs0.trans_le hsu'
  have ht0 : 0 < t.toReal := hu0.trans_le hut'
  have hlog : Real.log (t.toReal / s.toReal) =
      Real.log (t.toReal / u.toReal) + Real.log (u.toReal / s.toReal) := by
    rw [← Real.log_mul (div_pos ht0 hu0).ne' (div_pos hu0 hs0).ne']
    congr 1
    field_simp
  have h1 : 0 ≤ Real.log (t.toReal / u.toReal) :=
    Real.log_nonneg ((one_le_div hu0).2 hut')
  have h2 : 0 ≤ Real.log (u.toReal / s.toReal) :=
    Real.log_nonneg ((one_le_div hs0).2 hsu')
  rw [condTerm, condTerm, hlog, mul_add, ENNReal.ofReal_add (mul_nonneg hs0.le h1)
    (mul_nonneg hs0.le h2)]

theorem tsum_ofReal_toReal_mul {ι : Type*} {s : ι → ℝ≥0∞} (hs : ∀ i, s i ≠ ⊤) (L : ℝ) :
    ∑' i, ENNReal.ofReal ((s i).toReal * L) = (∑' i, s i) * ENNReal.ofReal L := by
  rw [← ENNReal.tsum_mul_right]
  refine tsum_congr fun i => ?_
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hs i)]

/-- **Countable log-sum inequality**: `∑ s_c log(t_c/s_c) ≤ S log(T/S)` for `s_c ≤ t_c`, with
`S = ∑ s_c`, `T = ∑ t_c < ∞`. -/
theorem tsum_condTerm_le {ι : Type*} {s t : ι → ℝ≥0∞} (hst : ∀ c, s c ≤ t c)
    (hT : ∑' c, t c ≠ ⊤) : ∑' c, condTerm (s c) (t c) ≤ condTerm (∑' c, s c) (∑' c, t c) := by
  set S := ∑' c, s c
  set T := ∑' c, t c
  have hST : S ≤ T := ENNReal.tsum_le_tsum hst
  have hS : S ≠ ⊤ := ne_top_of_le_ne_top hT hST
  have ht : ∀ c, t c ≠ ⊤ := fun c => ne_top_of_le_ne_top hT (ENNReal.le_tsum c)
  have hs : ∀ c, s c ≠ ⊤ := fun c => ne_top_of_le_ne_top (ht c) (hst c)
  by_cases hS0 : S = 0
  · have hzero : ∀ c, s c = 0 := fun c => (ENNReal.tsum_eq_zero.1 hS0) c
    simp [hzero, condTerm_zero_left]
  have hS0' : 0 < S.toReal := ENNReal.toReal_pos hS0 hS
  have hT0' : 0 < T.toReal := hS0'.trans_le (ENNReal.toReal_mono hT hST)
  set L := Real.log (T.toReal / S.toReal)
  set R := S.toReal / T.toReal
  have hL : 0 ≤ L := Real.log_nonneg ((one_le_div hS0').2 (ENNReal.toReal_mono hT hST))
  have hR : 0 ≤ R := div_nonneg hS0'.le hT0'.le
  -- termwise `s log(t/s) + s ≤ s log(T/S) + t S/T`, from `log x ≤ x - 1`
  have hterm : ∀ c, condTerm (s c) (t c) + s c ≤
      ENNReal.ofReal ((s c).toReal * L) + ENNReal.ofReal ((t c).toReal * R) := by
    intro c
    by_cases hc : s c = 0
    · rw [hc, condTerm_zero_left, zero_add]; exact zero_le
    have hsc : 0 < (s c).toReal := ENNReal.toReal_pos hc (hs c)
    have htc : (s c).toReal ≤ (t c).toReal := ENNReal.toReal_mono (ht c) (hst c)
    have htc0 : 0 < (t c).toReal := hsc.trans_le htc
    have hlogc : 0 ≤ Real.log ((t c).toReal / (s c).toReal) :=
      Real.log_nonneg ((one_le_div hsc).2 htc)
    have hx : 0 < (t c).toReal * S.toReal / ((s c).toReal * T.toReal) :=
      div_pos (mul_pos htc0 hS0') (mul_pos hsc hT0')
    have hlx := Real.log_le_sub_one_of_pos hx
    have hsplit : Real.log ((t c).toReal * S.toReal / ((s c).toReal * T.toReal)) =
        Real.log ((t c).toReal / (s c).toReal) - L := by
      rw [← Real.log_div (div_pos htc0 hsc).ne' (div_pos hT0' hS0').ne']
      congr 1
      field_simp
    rw [hsplit] at hlx
    have key := mul_le_mul_of_nonneg_left hlx hsc.le
    have hmul : (s c).toReal * ((t c).toReal * S.toReal / ((s c).toReal * T.toReal) - 1) =
        (t c).toReal * R - (s c).toReal := by
      simp only [R]
      field_simp
    rw [hmul] at key
    calc condTerm (s c) (t c) + s c
        = ENNReal.ofReal ((s c).toReal * Real.log ((t c).toReal / (s c).toReal) +
            (s c).toReal) := by
          rw [ENNReal.ofReal_add (mul_nonneg hsc.le hlogc) hsc.le, ENNReal.ofReal_toReal (hs c),
            condTerm]
      _ ≤ ENNReal.ofReal ((s c).toReal * L + (t c).toReal * R) :=
          ENNReal.ofReal_le_ofReal (by nlinarith [key])
      _ = _ := ENNReal.ofReal_add (mul_nonneg hsc.le hL) (mul_nonneg htc0.le hR)
  have hTS : T * ENNReal.ofReal R = S := by
    have hT' : T = ENNReal.ofReal T.toReal := (ENNReal.ofReal_toReal hT).symm
    calc T * ENNReal.ofReal R = ENNReal.ofReal T.toReal * ENNReal.ofReal R := by
          nth_rewrite 1 [hT']; rfl
      _ = ENNReal.ofReal (T.toReal * R) := (ENNReal.ofReal_mul hT0'.le).symm
      _ = S := by rw [mul_div_cancel₀ _ hT0'.ne', ENNReal.ofReal_toReal hS]
  have hfin : ∑' c, condTerm (s c) (t c) + S ≤ condTerm S T + S := by
    calc ∑' c, condTerm (s c) (t c) + S = ∑' c, (condTerm (s c) (t c) + s c) :=
          ENNReal.tsum_add.symm
      _ ≤ ∑' c, (ENNReal.ofReal ((s c).toReal * L) + ENNReal.ofReal ((t c).toReal * R)) :=
          ENNReal.tsum_le_tsum hterm
      _ = S * ENNReal.ofReal L + T * ENNReal.ofReal R := by
          rw [ENNReal.tsum_add, tsum_ofReal_toReal_mul hs L, tsum_ofReal_toReal_mul ht R]
      _ = condTerm S T + S := by
          rw [hTS, condTerm, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hS]
  exact ENNReal.le_of_add_le_add_right hS hfin

/-! ### Entropy of observables -/

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
variable {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
  [MeasurableSpace β] [MeasurableSingletonClass β] [Countable β]
  [MeasurableSpace γ] [MeasurableSingletonClass γ] [Countable γ]
  [MeasurableSpace δ] [MeasurableSingletonClass δ] [Countable δ]

/-- Shannon entropy `H_μ(f) = ∑_a η(μ{f = a})` of a countably-valued observable. -/
def obsEntropy (f : Ω → α) : ℝ≥0∞ := ∑' a, entropyTerm (μ (f ⁻¹' {a}))

/-- Conditional Shannon entropy `H_μ(f | g) = ∑_{a,b} μ{f=a, g=b} log(μ{g=b}/μ{f=a, g=b})`. -/
def obsCondEntropy (f : Ω → α) (g : Ω → β) : ℝ≥0∞ :=
  ∑' p : α × β, condTerm (μ (f ⁻¹' {p.1} ∩ g ⁻¹' {p.2})) (μ (g ⁻¹' {p.2}))

/-- The joint observable `(f, g)`. -/
def pairObs (f : Ω → α) (g : Ω → β) (ω : Ω) : α × β := (f ω, g ω)

omit [MeasurableSingletonClass α] [Countable α] [MeasurableSingletonClass β] [Countable β] in
theorem measurable_pairObs {f : Ω → α} {g : Ω → β} (hf : Measurable f) (hg : Measurable g) :
    Measurable (pairObs f g) := hf.prodMk hg

omit [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
  [MeasurableSpace β] [MeasurableSingletonClass β] [Countable β] in
theorem pairObs_preimage (f : Ω → α) (g : Ω → β) (a : α) (b : β) :
    pairObs f g ⁻¹' {(a, b)} = f ⁻¹' {a} ∩ g ⁻¹' {b} := by
  ext ω; simp [pairObs]

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem tsum_measure_fiber_inter {f : Ω → α} (hf : ∀ a, MeasurableSet (f ⁻¹' {a})) {B : Set Ω}
    (hB : MeasurableSet B) : ∑' a, μ (f ⁻¹' {a} ∩ B) = μ B := by
  rw [← measure_iUnion (fun a b hab => ?_) (fun a => (hf a).inter hB)]
  · congr 1
    ext ω; simp
  · refine Disjoint.mono inter_subset_left inter_subset_left ?_
    exact Set.disjoint_left.2 fun ω h1 h2 => hab (h1.symm.trans h2)

omit [Countable α] in
theorem measurableSet_fiber {f : Ω → α} (hf : Measurable f) (a : α) :
    MeasurableSet (f ⁻¹' {a}) := hf (measurableSet_singleton a)

omit [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α] [MeasurableSpace β]
  [MeasurableSingletonClass β] [Countable β] in
/-- Conditioning on a constant observable is no conditioning. -/
theorem obsCondEntropy_const [IsProbabilityMeasure μ] (f : Ω → α) (c : β) :
    obsCondEntropy μ f (fun _ => c) = obsEntropy μ f := by
  classical
  rw [obsCondEntropy, obsEntropy, ENNReal.tsum_prod']
  refine tsum_congr fun a => ?_
  rw [ENNReal.tsum_eq_add_tsum_ite c]
  have hrest : ∀ b, (if b = c then 0 else
      condTerm (μ (f ⁻¹' {a} ∩ (fun _ : Ω => c) ⁻¹' {b})) (μ ((fun _ : Ω => c) ⁻¹' {b}))) = 0 := by
    intro b
    split_ifs with hb
    · rfl
    · have : (fun _ : Ω => c) ⁻¹' {b} = ∅ := by
        ext ω; simp [Ne.symm hb]
      rw [this, inter_empty, measure_empty, condTerm_zero_left]
  rw [tsum_congr hrest, tsum_zero, add_zero]
  have : (fun _ : Ω => c) ⁻¹' {c} = univ := by ext; simp
  rw [this, inter_univ, measure_univ, condTerm_one_right]

/-! ### Relabelling -/

omit [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α] [MeasurableSpace β]
  [MeasurableSingletonClass β] [Countable β] [MeasurableSpace γ] [MeasurableSingletonClass γ]
  [Countable γ] in
/-- Injective relabelling of the conditioning observable. -/
theorem obsCondEntropy_comp_right {g : Ω → β} {φ : β → γ} (hφ : Function.Injective φ)
    (f : Ω → α) : obsCondEntropy μ f (φ ∘ g) = obsCondEntropy μ f g := by
  rw [obsCondEntropy, obsCondEntropy]
  have hinj : Function.Injective (Prod.map (id : α → α) φ) := Function.injective_id.prodMap hφ
  rw [← hinj.tsum_eq]
  · refine tsum_congr fun p => ?_
    simp only [Prod.map_fst, Prod.map_snd, id]
    have : (φ ∘ g) ⁻¹' {φ p.2} = g ⁻¹' {p.2} := by
      ext ω; simp [hφ.eq_iff]
    rw [this]
  · intro p hp
    by_contra hnot
    apply hp
    have hne : ∀ b, φ b ≠ p.2 := fun b hb => hnot ⟨(p.1, b), by simp [hb]⟩
    have : (φ ∘ g) ⁻¹' {p.2} = ∅ := by
      ext ω; simp [hne (g ω)]
    beta_reduce
    rw [this, inter_empty, measure_empty, condTerm_zero_left]

omit [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α] [MeasurableSpace β]
  [MeasurableSingletonClass β] [Countable β] [MeasurableSpace γ] [MeasurableSingletonClass γ]
  [Countable γ] in
/-- Injective relabelling of the conditioned observable. -/
theorem obsCondEntropy_comp_left {f : Ω → α} {φ : α → γ} (hφ : Function.Injective φ)
    (g : Ω → β) : obsCondEntropy μ (φ ∘ f) g = obsCondEntropy μ f g := by
  rw [obsCondEntropy, obsCondEntropy]
  have hinj : Function.Injective (Prod.map φ (id : β → β)) := hφ.prodMap Function.injective_id
  rw [← hinj.tsum_eq]
  · refine tsum_congr fun p => ?_
    simp only [Prod.map_fst, Prod.map_snd, id]
    have : (φ ∘ f) ⁻¹' {φ p.1} = f ⁻¹' {p.1} := by
      ext ω; simp [hφ.eq_iff]
    rw [this]
  · intro p hp
    by_contra hnot
    apply hp
    have hne : ∀ a, φ a ≠ p.1 := fun a ha => hnot ⟨(a, p.2), by simp [ha]⟩
    have : (φ ∘ f) ⁻¹' {p.1} = ∅ := by
      ext ω; simp [hne (f ω)]
    beta_reduce
    rw [this, empty_inter, measure_empty, condTerm_zero_left]

omit [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α] [MeasurableSpace γ]
  [MeasurableSingletonClass γ] [Countable γ] in
theorem obsEntropy_comp {f : Ω → α} {φ : α → γ} (hφ : Function.Injective φ) :
    obsEntropy μ (φ ∘ f) = obsEntropy μ f := by
  rw [obsEntropy, obsEntropy, ← hφ.tsum_eq]
  · refine tsum_congr fun a => ?_
    have : (φ ∘ f) ⁻¹' {φ a} = f ⁻¹' {a} := by
      ext ω; simp [hφ.eq_iff]
    rw [this]
  · intro c hc
    by_contra hnot
    apply hc
    have hne : ∀ a, φ a ≠ c := fun a ha => hnot ⟨a, ha⟩
    have : (φ ∘ f) ⁻¹' {c} = ∅ := by
      ext ω; simp [hne (f ω)]
    beta_reduce
    rw [this, measure_empty, entropyTerm, ENNReal.toReal_zero, Real.negMulLog_zero,
      ENNReal.ofReal_zero]

/-! ### The chain rule -/

omit [Countable β] [Countable γ] in
/-- **Conditional chain rule**: `H(f, g | k) = H(g | k) + H(f | g, k)`. -/
theorem obsCondEntropy_pairObs [IsFiniteMeasure μ] {f : Ω → α} {g : Ω → β} {k : Ω → γ}
    (hf : Measurable f) (hg : Measurable g) (hk : Measurable k) :
    obsCondEntropy μ (pairObs f g) k =
      obsCondEntropy μ g k + obsCondEntropy μ f (pairObs g k) := by
  have hsplit : ∀ (a : α) (b : β) (c : γ),
      condTerm (μ (pairObs f g ⁻¹' {(a, b)} ∩ k ⁻¹' {c})) (μ (k ⁻¹' {c})) =
        ENNReal.ofReal ((μ (f ⁻¹' {a} ∩ pairObs g k ⁻¹' {(b, c)})).toReal *
          Real.log ((μ (k ⁻¹' {c})).toReal / (μ (g ⁻¹' {b} ∩ k ⁻¹' {c})).toReal)) +
        condTerm (μ (f ⁻¹' {a} ∩ pairObs g k ⁻¹' {(b, c)})) (μ (pairObs g k ⁻¹' {(b, c)})) := by
    intro a b c
    have hset : pairObs f g ⁻¹' {(a, b)} ∩ k ⁻¹' {c} = f ⁻¹' {a} ∩ pairObs g k ⁻¹' {(b, c)} := by
      rw [pairObs_preimage, pairObs_preimage, inter_assoc]
    rw [hset, pairObs_preimage g k]
    exact condTerm_split (measure_mono inter_subset_right) (measure_mono inter_subset_right)
      (measure_ne_top _ _)
  rw [obsCondEntropy]
  rw [show (∑' p : (α × β) × γ, condTerm (μ (pairObs f g ⁻¹' {p.1} ∩ k ⁻¹' {p.2}))
      (μ (k ⁻¹' {p.2}))) = ∑' p : (α × β) × γ, condTerm (μ (pairObs f g ⁻¹' {(p.1.1, p.1.2)} ∩
        k ⁻¹' {p.2})) (μ (k ⁻¹' {p.2})) from rfl]
  simp_rw [hsplit]
  rw [ENNReal.tsum_add]
  congr 1
  · -- the first part sums over `a` to `H(g | k)`
    rw [obsCondEntropy, ← ((Equiv.prodComm (β × γ) α).trans
      (Equiv.prodAssoc α β γ).symm).tsum_eq, ENNReal.tsum_prod']
    refine tsum_congr fun q => ?_
    simp only [Equiv.trans_apply, Equiv.prodComm_apply, Prod.swap_prod_mk,
      Equiv.prodAssoc_symm_apply]
    rw [tsum_ofReal_toReal_mul (fun _ => measure_ne_top _ _),
      tsum_measure_fiber_inter μ (measurableSet_fiber hf)
        (measurableSet_fiber (measurable_pairObs hg hk) _), pairObs_preimage, condTerm,
      ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  · rw [obsCondEntropy, ← (Equiv.prodAssoc α β γ).tsum_eq]
    rfl

omit [Countable β] in
/-- The chain rule `H(f, g) = H(g) + H(f | g)`. -/
theorem obsEntropy_pairObs [IsProbabilityMeasure μ] {f : Ω → α} {g : Ω → β}
    (hf : Measurable f) (hg : Measurable g) :
    obsEntropy μ (pairObs f g) = obsEntropy μ g + obsCondEntropy μ f g := by
  have h := obsCondEntropy_pairObs μ hf hg (measurable_const (a := ()))
  rw [obsCondEntropy_const, obsCondEntropy_const] at h
  rw [h]
  congr 1
  have hinj : Function.Injective fun b : β => (b, ()) := fun x y hxy => (Prod.ext_iff.1 hxy).1
  exact obsCondEntropy_comp_right μ hinj f

/-! ### Conditioning reduces entropy -/

omit [Countable α] [Countable β] in
/-- **Conditioning reduces entropy**: `H(f | g, k) ≤ H(f | g)`. -/
theorem obsCondEntropy_pairObs_le [IsFiniteMeasure μ] {f : Ω → α} {g : Ω → β} {k : Ω → γ}
    (hf : Measurable f) (hg : Measurable g) (hk : Measurable k) :
    obsCondEntropy μ f (pairObs g k) ≤ obsCondEntropy μ f g := by
  rw [obsCondEntropy, obsCondEntropy, ← (Equiv.prodAssoc α β γ).tsum_eq, ENNReal.tsum_prod']
  refine ENNReal.tsum_le_tsum fun q => ?_
  have hjoint : ∑' c, μ (f ⁻¹' {q.1} ∩ pairObs g k ⁻¹' {(q.2, c)}) =
      μ (f ⁻¹' {q.1} ∩ g ⁻¹' {q.2}) := by
    rw [← tsum_measure_fiber_inter μ (measurableSet_fiber hk)
      ((measurableSet_fiber hf _).inter (measurableSet_fiber hg _))]
    refine tsum_congr fun c => ?_
    rw [pairObs_preimage]
    congr 1
    ext ω; simp only [mem_inter_iff, mem_preimage]; tauto
  have hcond : ∑' c, μ (pairObs g k ⁻¹' {(q.2, c)}) = μ (g ⁻¹' {q.2}) := by
    rw [← tsum_measure_fiber_inter μ (measurableSet_fiber hk) (measurableSet_fiber hg _)]
    refine tsum_congr fun c => ?_
    rw [pairObs_preimage, inter_comm]
  have h := tsum_condTerm_le (s := fun c => μ (f ⁻¹' {q.1} ∩ pairObs g k ⁻¹' {(q.2, c)}))
    (t := fun c => μ (pairObs g k ⁻¹' {(q.2, c)})) (fun c => measure_mono inter_subset_right)
    (by rw [hcond]; exact measure_ne_top _ _)
  rw [hjoint, hcond] at h
  exact h

omit [Countable α] [Countable γ] in
/-- Conditioning on a coarser observable gives larger conditional entropy. -/
theorem obsCondEntropy_le_comp [IsFiniteMeasure μ] {f : Ω → α} {g : Ω → β} (hf : Measurable f)
    (hg : Measurable g) (φ : β → γ) :
    obsCondEntropy μ f g ≤ obsCondEntropy μ f (φ ∘ g) := by
  have hinj : Function.Injective fun b : β => (φ b, b) := fun x y hxy => (Prod.ext_iff.1 hxy).2
  have h := obsCondEntropy_comp_right μ hinj f (g := g)
  rw [← h]
  exact obsCondEntropy_pairObs_le μ hf ((measurable_of_countable φ).comp hg) hg

omit [Countable α] in
/-- `H(f | g) ≤ H(f)`. -/
theorem obsCondEntropy_le_obsEntropy [IsProbabilityMeasure μ] {f : Ω → α} {g : Ω → β}
    (hf : Measurable f) (hg : Measurable g) : obsCondEntropy μ f g ≤ obsEntropy μ f := by
  rw [← obsCondEntropy_const μ f ()]
  exact obsCondEntropy_le_comp μ hf hg (fun _ => ())

omit [Countable γ] in
/-- Coarsening decreases entropy: `H(φ ∘ f) ≤ H(f)`. -/
theorem obsEntropy_comp_le [IsProbabilityMeasure μ] {f : Ω → α} (hf : Measurable f)
    (φ : α → γ) : obsEntropy μ (φ ∘ f) ≤ obsEntropy μ f := by
  have hinj : Function.Injective fun a : α => (a, φ a) := fun x y hxy => (Prod.ext_iff.1 hxy).1
  rw [← obsEntropy_comp μ hinj (f := f)]
  have hpair : (fun a : α => (a, φ a)) ∘ f = pairObs f (φ ∘ f) := rfl
  rw [hpair, obsEntropy_pairObs μ hf ((measurable_of_countable φ).comp hf)]
  exact le_self_add

/-- `H(f) ≤ H(f, g)`. -/
theorem obsEntropy_le_pairObs [IsProbabilityMeasure μ] {f : Ω → α} {g : Ω → β}
    (hf : Measurable f) (hg : Measurable g) : obsEntropy μ f ≤ obsEntropy μ (pairObs f g) :=
  obsEntropy_comp_le μ (measurable_pairObs hf hg) Prod.fst

/-- Subadditivity `H(f, g) ≤ H(f) + H(g)`. -/
theorem obsEntropy_pairObs_le [IsProbabilityMeasure μ] {f : Ω → α} {g : Ω → β}
    (hf : Measurable f) (hg : Measurable g) :
    obsEntropy μ (pairObs f g) ≤ obsEntropy μ f + obsEntropy μ g := by
  rw [obsEntropy_pairObs μ hf hg, add_comm (obsEntropy μ f)]
  exact add_le_add le_rfl (obsCondEntropy_le_obsEntropy μ hf hg)

/-- Conditional subadditivity `H(f, g | k) ≤ H(f | k) + H(g | k)`. -/
theorem obsCondEntropy_pairObs_le_add [IsFiniteMeasure μ] {f : Ω → α} {g : Ω → β} {k : Ω → γ}
    (hf : Measurable f) (hg : Measurable g) (hk : Measurable k) :
    obsCondEntropy μ (pairObs f g) k ≤ obsCondEntropy μ f k + obsCondEntropy μ g k := by
  rw [obsCondEntropy_pairObs μ hf hg hk, add_comm (obsCondEntropy μ f k)]
  exact add_le_add le_rfl (obsCondEntropy_le_comp μ hf (measurable_pairObs hg hk) Prod.snd)

/-! ### Invariance -/

omit [Countable α] [Countable β] in
/-- Conditional entropy depends only on the joint law: invariance under measure-preserving maps. -/
theorem obsCondEntropy_comp_measurePreserving {Ω' : Type*} [MeasurableSpace Ω'] {ν : Measure Ω'}
    {T : Ω → Ω'} (hT : MeasurePreserving T μ ν) {f : Ω' → α} {g : Ω' → β}
    (hf : Measurable f) (hg : Measurable g) :
    obsCondEntropy μ (f ∘ T) (g ∘ T) = obsCondEntropy ν f g := by
  rw [obsCondEntropy, obsCondEntropy]
  refine tsum_congr fun p => ?_
  rw [preimage_comp, preimage_comp, ← preimage_inter,
    hT.measure_preimage ((hf (measurableSet_singleton _)).inter
      (hg (measurableSet_singleton _))).nullMeasurableSet,
    hT.measure_preimage (hg (measurableSet_singleton _)).nullMeasurableSet]

omit [Countable α] in
theorem obsEntropy_comp_measurePreserving {Ω' : Type*} [MeasurableSpace Ω'] {ν : Measure Ω'}
    {T : Ω → Ω'} (hT : MeasurePreserving T μ ν) {f : Ω' → α} (hf : Measurable f) :
    obsEntropy μ (f ∘ T) = obsEntropy ν f := by
  rw [obsEntropy, obsEntropy]
  refine tsum_congr fun a => ?_
  rw [preimage_comp, hT.measure_preimage (hf (measurableSet_singleton _)).nullMeasurableSet]

omit [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α] [MeasurableSpace β]
  [MeasurableSingletonClass β] [Countable β] in
/-- Conditional entropy is unchanged by a.e. modification of the observables. -/
theorem obsCondEntropy_congr_ae {f f' : Ω → α} {g g' : Ω → β} (hf : f =ᵐ[μ] f')
    (hg : g =ᵐ[μ] g') : obsCondEntropy μ f g = obsCondEntropy μ f' g' := by
  rw [obsCondEntropy, obsCondEntropy]
  refine tsum_congr fun p => ?_
  have h1 : f ⁻¹' {p.1} =ᵐ[μ] f' ⁻¹' {p.1} := by
    filter_upwards [hf] with ω hω
    change (f ω ∈ ({p.1} : Set α)) = (f' ω ∈ ({p.1} : Set α))
    rw [hω]
  have h2 : g ⁻¹' {p.2} =ᵐ[μ] g' ⁻¹' {p.2} := by
    filter_upwards [hg] with ω hω
    change (g ω ∈ ({p.2} : Set β)) = (g' ω ∈ ({p.2} : Set β))
    rw [hω]
  rw [measure_congr (h1.inter h2), measure_congr h2]

omit [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α] in
theorem obsEntropy_congr_ae {f f' : Ω → α} (hf : f =ᵐ[μ] f') :
    obsEntropy μ f = obsEntropy μ f' := by
  rw [obsEntropy, obsEntropy]
  refine tsum_congr fun a => ?_
  have h1 : f ⁻¹' {a} =ᵐ[μ] f' ⁻¹' {a} := by
    filter_upwards [hf] with ω hω
    change (f ω ∈ ({a} : Set α)) = (f' ω ∈ ({a} : Set α))
    rw [hω]
  rw [measure_congr h1]

/-! ### Independence -/

omit [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α] in
/-- For independent observables `H(f | g) = H(f)`. -/
theorem obsCondEntropy_of_indep [IsProbabilityMeasure μ] {f : Ω → α} {g : Ω → β}
    (hg : Measurable g)
    (h : ∀ a b, μ (f ⁻¹' {a} ∩ g ⁻¹' {b}) = μ (f ⁻¹' {a}) * μ (g ⁻¹' {b})) :
    obsCondEntropy μ f g = obsEntropy μ f := by
  have hterm : ∀ a b, condTerm (μ (f ⁻¹' {a} ∩ g ⁻¹' {b})) (μ (g ⁻¹' {b})) =
      μ (g ⁻¹' {b}) * entropyTerm (μ (f ⁻¹' {a})) := by
    intro a b
    rw [h]
    set x := μ (f ⁻¹' {a})
    set y := μ (g ⁻¹' {b})
    by_cases hy : y.toReal = 0
    · have hy0 : y = 0 := (ENNReal.toReal_eq_zero_iff y).1 hy |>.resolve_right (measure_ne_top _ _)
      rw [hy0, mul_zero, zero_mul, condTerm_zero_left]
    have hy0 : 0 < y.toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hy)
    rw [condTerm, entropyTerm, ENNReal.toReal_mul, ← ENNReal.ofReal_toReal (a := y)
      (measure_ne_top _ _), ← ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.toReal_ofReal
      ENNReal.toReal_nonneg]
    congr 1
    by_cases hx : x.toReal = 0
    · rw [hx]; simp
    rw [show y.toReal / (x.toReal * y.toReal) = (x.toReal)⁻¹ by field_simp, Real.log_inv,
      Real.negMulLog]
    ring
  rw [obsCondEntropy, obsEntropy, ENNReal.tsum_prod']
  refine tsum_congr fun a => ?_
  simp_rw [hterm a, ENNReal.tsum_mul_right]
  have hone : ∑' b, μ (g ⁻¹' {b}) = 1 := by
    have := tsum_measure_fiber_inter μ (measurableSet_fiber hg) MeasurableSet.univ
    simpa using this
  rw [hone, one_mul]

/-- For independent observables `H(f, g) = H(f) + H(g)`. -/
theorem obsEntropy_pairObs_of_indep [IsProbabilityMeasure μ] {f : Ω → α} {g : Ω → β}
    (hf : Measurable f) (hg : Measurable g)
    (h : ∀ a b, μ (f ⁻¹' {a} ∩ g ⁻¹' {b}) = μ (f ⁻¹' {a}) * μ (g ⁻¹' {b})) :
    obsEntropy μ (pairObs f g) = obsEntropy μ f + obsEntropy μ g := by
  rw [obsEntropy_pairObs μ hf hg, obsCondEntropy_of_indep μ hg h, add_comm]

end GaloisForLFunctions.HTGeometry.ObservableEntropy
