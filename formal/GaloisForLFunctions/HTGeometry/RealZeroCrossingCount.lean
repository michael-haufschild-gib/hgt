import Mathlib

/-!
# Zero crossings of real functions with local factorizations

A real function has local factor data `(m, g)` at `ζ` when `f(t) = (t - ζ)^m g(t)` near `ζ`, with
`g` continuous at `ζ` and `g(ζ) ≠ 0`.  A simple factor has derivative `g(ζ)`, a factor of order at
least two has derivative zero, and a positive-slope simple zero is an up-crossing.  Between two
positive-slope simple zeros the last positive point of a sign change is a zero of odd order at
which `f` passes from positive to negative values.  Finally, if every two points of a finite set
`U` are separated by a point of `W`, then `|U| ≤ |W| + 1`.
-/

open Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- A real function has local factor data `(m, g)` at `ζ` when `f(t) = (t - ζ)^m g(t)` near `ζ`,
with `g` continuous at `ζ` and `g(ζ) ≠ 0`. -/
def HasLocalZeroFactor (f : ℝ → ℝ) (ζ : ℝ) (m : ℕ) (g : ℝ → ℝ) : Prop :=
  ContinuousAt g ζ ∧ g ζ ≠ 0 ∧ ∀ᶠ t in 𝓝 ζ, f t = (t - ζ) ^ m * g t

theorem HasLocalZeroFactor.neg {f g : ℝ → ℝ} {ζ : ℝ} {m : ℕ} (h : HasLocalZeroFactor f ζ m g) :
    HasLocalZeroFactor (fun t => -f t) ζ m (fun t => -g t) :=
  ⟨h.1.neg, neg_ne_zero.mpr h.2.1, h.2.2.mono fun t ht => by simp only; rw [ht]; ring⟩

theorem HasLocalZeroFactor.apply_eq {f g : ℝ → ℝ} {ζ : ℝ} {m : ℕ} (h : HasLocalZeroFactor f ζ m g) :
    f ζ = 0 ^ m * g ζ := by
  have := h.2.2.self_of_nhds
  rwa [sub_self] at this

theorem HasLocalZeroFactor.pos_of_eq_zero {f g : ℝ → ℝ} {ζ : ℝ} {m : ℕ}
    (h : HasLocalZeroFactor f ζ m g) (h0 : f ζ = 0) : 0 < m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [h.apply_eq, pow_zero, one_mul] at h0; exact absurd h0 h.2.1
  · exact hm

/-- A simple factor gives the derivative `g(ζ)`. -/
theorem HasLocalZeroFactor.hasDerivAt_one {f g : ℝ → ℝ} {ζ : ℝ} (h : HasLocalZeroFactor f ζ 1 g) :
    HasDerivAt f (g ζ) ζ := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hf0 : f ζ = 0 := by rw [h.apply_eq]; simp
  refine (h.1.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [nhdsWithin_le_nhds h.2.2, self_mem_nhdsWithin] with t ht htne
  rw [slope_def_field, ht, hf0, pow_one, sub_zero]
  field_simp [sub_ne_zero.mpr htne]

/-- A factor of order at least two gives derivative zero. -/
theorem HasLocalZeroFactor.hasDerivAt_of_two_le {f g : ℝ → ℝ} {ζ : ℝ} {m : ℕ}
    (h : HasLocalZeroFactor f ζ m g) (hm : 2 ≤ m) : HasDerivAt f 0 ζ := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hf0 : f ζ = 0 := by rw [h.apply_eq, zero_pow (by omega), zero_mul]
  have hlim : Tendsto (fun t => (t - ζ) ^ (m - 1) * g t) (𝓝 ζ) (𝓝 0) := by
    have := ((continuous_sub_right ζ).pow (m - 1)).continuousAt.tendsto.mul h.1.tendsto
    simpa [zero_pow (show m - 1 ≠ 0 by omega)] using this
  refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [nhdsWithin_le_nhds h.2.2, self_mem_nhdsWithin] with t ht htne
  rw [slope_def_field, ht, hf0, sub_zero]
  have hne : t - ζ ≠ 0 := sub_ne_zero.mpr htne
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  field_simp
  ring

/-- If `f(ζ) = 0` and `f'(ζ) = d > 0` then the factor is simple with `g(ζ) = d`. -/
theorem HasLocalZeroFactor.eq_one_of_hasDerivAt {f g : ℝ → ℝ} {ζ d : ℝ} {m : ℕ}
    (h : HasLocalZeroFactor f ζ m g) (h0 : f ζ = 0) (hd : HasDerivAt f d ζ) (hd0 : d ≠ 0) :
    m = 1 ∧ g ζ = d := by
  have hm := h.pos_of_eq_zero h0
  rcases (show m = 1 ∨ 2 ≤ m by omega) with rfl | h2
  · exact ⟨rfl, (h.hasDerivAt_one).unique hd⟩
  · exact absurd ((h.hasDerivAt_of_two_le h2).unique hd).symm hd0

/-- Sign near a simple positive-slope zero: `f > 0` just right and `f < 0` just left. -/
theorem HasLocalZeroFactor.eventually_pos_right {f g : ℝ → ℝ} {ζ : ℝ}
    (h : HasLocalZeroFactor f ζ 1 g) (hg : 0 < g ζ) :
    (∀ᶠ t in 𝓝[>] ζ, 0 < f t) ∧ ∀ᶠ t in 𝓝[<] ζ, f t < 0 := by
  have hgpos : ∀ᶠ t in 𝓝 ζ, 0 < g t := h.1.eventually (lt_mem_nhds hg)
  constructor
  · filter_upwards [nhdsWithin_le_nhds h.2.2, nhdsWithin_le_nhds hgpos, self_mem_nhdsWithin]
      with t ht hg' hlt
    rw [ht, pow_one]; exact mul_pos (sub_pos.mpr hlt) hg'
  · filter_upwards [nhdsWithin_le_nhds h.2.2, nhdsWithin_le_nhds hgpos, self_mem_nhdsWithin]
      with t ht hg' hlt
    rw [ht, pow_one]; exact mul_neg_of_neg_of_pos (sub_neg.mpr hlt) hg'

/-- **Down-crossing between two up-crossings.** If `f` is continuous, has local factor data of
order `ord ζ` at every point, and has simple zeros with positive slope at `γ₁ < γ₂`, then between
them there is a zero `ζ` of odd order at which `f` passes from positive to negative values. -/
theorem exists_down_crossing_between {f : ℝ → ℝ} (hf : Continuous f) (ord : ℝ → ℕ)
    (hfac : ∀ ζ, ∃ g, HasLocalZeroFactor f ζ (ord ζ) g) {γ₁ γ₂ d₁ d₂ : ℝ} (h12 : γ₁ < γ₂)
    (h1 : f γ₁ = 0) (hd1 : HasDerivAt f d₁ γ₁) (hd10 : 0 < d₁)
    (h2 : f γ₂ = 0) (hd2 : HasDerivAt f d₂ γ₂) (hd20 : 0 < d₂) :
    ∃ ζ ∈ Ioo γ₁ γ₂, f ζ = 0 ∧ Odd (ord ζ) ∧ ∃ g, HasLocalZeroFactor f ζ (ord ζ) g ∧ g ζ < 0 := by
  obtain ⟨g₁, hg₁⟩ := hfac γ₁
  obtain ⟨g₂, hg₂⟩ := hfac γ₂
  obtain ⟨ho1, hg1v⟩ := hg₁.eq_one_of_hasDerivAt h1 hd1 hd10.ne'
  obtain ⟨ho2, hg2v⟩ := hg₂.eq_one_of_hasDerivAt h2 hd2 hd20.ne'
  rw [ho1] at hg₁
  rw [ho2] at hg₂
  have s1 := (hg₁.eventually_pos_right (by rw [hg1v]; exact hd10)).1
  have s2 := (hg₂.eventually_pos_right (by rw [hg2v]; exact hd20)).2
  -- a positive point `p` and a later negative point `q`
  obtain ⟨p, hp, hpγ⟩ := ((s1.and (Ioo_mem_nhdsGT h12)).exists)
  obtain ⟨q, hq, hqγ⟩ := ((s2.and (Ioo_mem_nhdsLT hpγ.2)).exists)
  have hpq : p < q := hqγ.1
  set S : Set ℝ := {t | t ∈ Icc p q ∧ 0 < f t} with hSdef
  have hSne : S.Nonempty := ⟨p, ⟨le_refl p, hpq.le⟩, hp⟩
  have hSbdd : BddAbove S := ⟨q, fun t ht => ht.1.2⟩
  set ζ := sSup S with hζ
  have hpζ : p ≤ ζ := le_csSup hSbdd ⟨⟨le_refl p, hpq.le⟩, hp⟩
  have hζq : ζ ≤ q := csSup_le hSne fun t ht => ht.1.2
  have hcl : ζ ∈ closure S := csSup_mem_closure hSne hSbdd
  have hζnn : 0 ≤ f ζ := by
    have hsub : closure S ⊆ {t | 0 ≤ f t} :=
      closure_minimal (fun t ht => ht.2.le) (isClosed_le continuous_const hf)
    exact hsub hcl
  have hright : ∀ t ∈ Ioc ζ q, f t ≤ 0 := by
    intro t ht
    by_contra hpos
    rw [not_le] at hpos
    have := le_csSup hSbdd ⟨⟨hpζ.trans ht.1.le, ht.2⟩, hpos⟩
    linarith [ht.1]
  have hζlt : ζ < q := lt_of_le_of_ne hζq fun h => by rw [h] at hζnn; linarith
  have hζ0 : f ζ = 0 := by
    refine le_antisymm ?_ hζnn
    have hlim : Tendsto f (𝓝[>] ζ) (𝓝 (f ζ)) := hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT hζlt] with t ht
    exact hright t ⟨ht.1, ht.2.le⟩
  have hpζ' : p < ζ := lt_of_le_of_ne hpζ fun h => by rw [← h] at hζ0; linarith
  refine ⟨ζ, ⟨lt_trans hpγ.1 hpζ', lt_trans hζlt hqγ.2⟩, hζ0, ?_⟩
  obtain ⟨g, hg⟩ := hfac ζ
  have hm := hg.pos_of_eq_zero hζ0
  -- right side forces `g ζ ≤ 0`
  have hgle : g ζ ≤ 0 := by
    have hlim : Tendsto g (𝓝[>] ζ) (𝓝 (g ζ)) := hg.1.tendsto.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto hlim ?_
    filter_upwards [nhdsWithin_le_nhds hg.2.2, Ioo_mem_nhdsGT hζlt] with t ht htI
    have hpow : 0 < (t - ζ) ^ ord ζ := pow_pos (sub_pos.mpr htI.1) _
    have := hright t ⟨htI.1, htI.2.le⟩
    rw [ht] at this
    exact nonpos_of_mul_nonpos_right this hpow
  have hgneg : g ζ < 0 := lt_of_le_of_ne hgle hg.2.1
  refine ⟨?_, g, hg, hgneg⟩
  -- left side: points arbitrarily close with `f > 0`
  by_contra hodd
  have heven : Even (ord ζ) := Nat.not_odd_iff_even.mp hodd
  have hgev : ∀ᶠ t in 𝓝 ζ, g t < 0 := hg.1.eventually (gt_mem_nhds hgneg)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (hgev.and hg.2.2)
  obtain ⟨s, hsS, hs⟩ := exists_lt_of_lt_csSup hSne (show ζ - δ < ζ by linarith)
  have hsle : s ≤ ζ := le_csSup hSbdd hsS
  have hdist : dist s ζ < δ := by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith
  obtain ⟨hgs, hfs⟩ := hball hdist
  have := hsS.2
  rw [hfs] at this
  have h1 := heven.pow_nonneg (s - ζ)
  nlinarith

/-- **Separation counting.** If every two points of `U` are separated by a point of `W`, then
`|U| ≤ |W| + 1`. -/
theorem card_le_card_add_one_of_separated (U W : Finset ℝ)
    (h : ∀ u ∈ U, ∀ u' ∈ U, u < u' → ∃ w ∈ W, u < w ∧ w < u') : U.card ≤ W.card + 1 := by
  classical
  induction U using Finset.induction_on_max generalizing W with
  | empty => simp
  | insert a s has ih =>
    rcases s.eq_empty_or_nonempty with rfl | hne
    · simp
    · set m := s.max' hne
      have hm : m ∈ s := s.max'_mem hne
      obtain ⟨w₀, hw₀, hmw, hwa⟩ := h m (Finset.mem_insert_of_mem hm) a
        (Finset.mem_insert_self a s) (has m hm)
      have hsub := ih (W.filter (· < w₀)) fun u hu u' hu' huu' => by
        obtain ⟨w, hw, h1, h2⟩ := h u (Finset.mem_insert_of_mem hu) u'
          (Finset.mem_insert_of_mem hu') huu'
        refine ⟨w, Finset.mem_filter.mpr ⟨hw, lt_of_lt_of_le h2 ?_ |>.trans hmw⟩, h1, h2⟩
        exact s.le_max' u' hu'
      have hlt : (W.filter (· < w₀)).card < W.card :=
        Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨w₀, hw₀, lt_irrefl _⟩)
      have hna : a ∉ s := fun ha => lt_irrefl a (has a ha)
      rw [Finset.card_insert_of_notMem hna]
      omega

end GaloisForLFunctions.HTGeometry
