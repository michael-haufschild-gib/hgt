import GaloisForLFunctions.HTGeometry.RealRootedCoefficientLimit

/-!
# Reality leaves only through collision

A finite configuration symmetric under conjugation is the zero set of a real polynomial, and all of
its points are real exactly when the polynomial is real-rooted (`Polynomial.Splits` over `ℝ`). This
module proves the finite-dimensional deformation principle of the field: along a continuous family
of real polynomials of fixed degree, reality can only be lost at a collision.

* **Simple real configurations are stable** (`eventually_splits_of_simple`). If `P t₀` is
  real-rooted of degree `n` with no root shared by `P t₀` and its derivative, then `P t` is
  real-rooted for all `t` near `t₀`. Each simple root changes sign (`exists_sign_change`); the sign
  changes persist, and by the intermediate value theorem `P t` keeps `n` distinct real roots.
* **Reality is closed** (`isClosed_splits`). Coefficient limits of real-rooted polynomials of
  bounded degree are real-rooted (`HTGeometry.splits_of_tendsto_coeff`).
* **The exit theorem** (`exists_first_collision`). If `P 0` is real-rooted and `P 1` is not, there
  is a first exit time `τ ∈ [0, 1)`: every `P s` with `s ≤ τ` is real-rooted, and `P τ` has a
  collision — a real double root.

The statement uses no sign of a form, no spectrum and no count of zeros: it is a continuation
argument. For `ζ` its counterpart is the de Bruijn–Newman collision criterion
(`RHTower.riemannHypothesis_iff_forall_zeros_simple`): there the deformation is the heat flow and
reality at `t = 0` is RH.
-/

open Polynomial Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

/-- A **collision**: a real point where `p` and `p'` both vanish. -/
def IsCollision (p : ℝ[X]) : Prop := ∃ x : ℝ, p.IsRoot x ∧ p.derivative.IsRoot x

/-- **A simple root changes sign.** -/
theorem exists_sign_change {p : ℝ[X]} {r : ℝ} (hr : p.IsRoot r) (hd : p.derivative.eval r ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), p.eval (r - ε) * p.eval (r + ε) < 0 := by
  have hr0 : p.eval r = 0 := hr
  rcases lt_or_gt_of_ne hd with hneg | hpos
  · have hev : ∀ᶠ x in 𝓝 r, p.derivative.eval x < 0 :=
      p.derivative.continuous.continuousAt.eventually_lt continuousAt_const hneg
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
    have hanti : StrictAntiOn (fun x => p.eval x) (Icc (r - δ / 2) (r + δ / 2)) := by
      refine strictAntiOn_of_deriv_neg (convex_Icc _ _) p.continuous.continuousOn fun x hx => ?_
      rw [interior_Icc] at hx
      rw [Polynomial.deriv]
      exact hball (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hx.1, hx.2])
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < δ / 2 by linarith)] with ε hε
    have h1 : p.eval r < p.eval (r - ε) :=
      hanti ⟨by linarith [hε.2], by linarith [hε.1]⟩ ⟨by linarith, by linarith⟩ (by linarith [hε.1])
    have h2 : p.eval (r + ε) < p.eval r :=
      hanti ⟨by linarith, by linarith⟩ ⟨by linarith [hε.1], by linarith [hε.2]⟩ (by linarith [hε.1])
    rw [hr0] at h1 h2
    nlinarith
  · have hev : ∀ᶠ x in 𝓝 r, 0 < p.derivative.eval x :=
      continuousAt_const.eventually_lt p.derivative.continuous.continuousAt hpos
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
    have hmono : StrictMonoOn (fun x => p.eval x) (Icc (r - δ / 2) (r + δ / 2)) := by
      refine strictMonoOn_of_deriv_pos (convex_Icc _ _) p.continuous.continuousOn fun x hx => ?_
      rw [interior_Icc] at hx
      rw [Polynomial.deriv]
      exact hball (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hx.1, hx.2])
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < δ / 2 by linarith)] with ε hε
    have h1 : p.eval (r - ε) < p.eval r :=
      hmono ⟨by linarith [hε.2], by linarith [hε.1]⟩ ⟨by linarith, by linarith⟩ (by linarith [hε.1])
    have h2 : p.eval r < p.eval (r + ε) :=
      hmono ⟨by linarith, by linarith⟩ ⟨by linarith [hε.1], by linarith [hε.2]⟩ (by linarith [hε.1])
    rw [hr0] at h1 h2
    nlinarith

/-- A sign change of a real polynomial on `[a, b]` produces a root in `(a, b)`. -/
theorem exists_root_Ioo_of_mul_neg (q : ℝ[X]) {a b : ℝ} (hab : a ≤ b)
    (h : q.eval a * q.eval b < 0) : ∃ x ∈ Ioo a b, q.IsRoot x := by
  rcases lt_or_gt_of_ne (show q.eval a ≠ 0 by rintro h0; simp [h0] at h) with ha | ha
  · have hb : 0 < q.eval b := by nlinarith
    obtain ⟨x, hx, hx0⟩ := intermediate_value_Ioo hab q.continuous.continuousOn ⟨ha, hb⟩
    exact ⟨x, hx, hx0⟩
  · have hb : q.eval b < 0 := by nlinarith
    obtain ⟨x, hx, hx0⟩ := intermediate_value_Ioo' hab q.continuous.continuousOn ⟨hb, ha⟩
    exact ⟨x, hx, hx0⟩

/-- Evaluation of a family of bounded degree is continuous in the parameter. -/
theorem continuous_eval_family {P : ℝ → ℝ[X]} {n : ℕ} (hdeg : ∀ t, (P t).natDegree ≤ n)
    (hcont : ∀ j, Continuous fun t => (P t).coeff j) (x : ℝ) :
    Continuous fun t => (P t).eval x := by
  have h : (fun t => (P t).eval x) = fun t => ∑ i ∈ Finset.range (n + 1), (P t).coeff i * x ^ i :=
    funext fun t => eval_eq_sum_range' (Nat.lt_succ_of_le (hdeg t)) x
  rw [h]
  exact continuous_finsetSum _ fun i _ => (hcont i).mul continuous_const

/-- **Simple real configurations are stable.** -/
theorem eventually_splits_of_simple {P : ℝ → ℝ[X]} {n : ℕ} (hdeg : ∀ t, (P t).natDegree ≤ n)
    (hcont : ∀ j, Continuous fun t => (P t).coeff j) {t₀ : ℝ} (hsplit : (P t₀).Splits)
    (hn : (P t₀).natDegree = n) (hsimple : ¬ IsCollision (P t₀)) :
    ∀ᶠ t in 𝓝 t₀, (P t).Splits := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · exact Eventually.of_forall fun t => splits_iff_card_roots.mpr (by
      have := card_roots' (P t); have := hdeg t; omega)
  set p := P t₀ with hp
  have hp0 : p ≠ 0 := fun h => by rw [h, natDegree_zero] at hn; omega
  set R := p.roots.toFinset with hR
  have hroot : ∀ r ∈ R, p.IsRoot r := fun r hr =>
    (mem_roots hp0).mp (Multiset.mem_toFinset.mp hr)
  have hderiv : ∀ r ∈ R, p.derivative.eval r ≠ 0 := fun r hr h => hsimple ⟨r, hroot r hr, h⟩
  have hnodup : p.roots.Nodup := by
    refine Multiset.nodup_iff_count_le_one.mpr fun r => ?_
    rw [count_roots]
    by_contra h
    push Not at h
    exact hsimple ⟨r, ((one_lt_rootMultiplicity_iff_isRoot hp0).mp h).1,
      ((one_lt_rootMultiplicity_iff_isRoot hp0).mp h).2⟩
  have hcard : R.card = n := by
    rw [hR, Multiset.toFinset_card_of_nodup hnodup, splits_iff_card_roots.mp hsplit, hn]
  -- one radius `ε` for all roots: sign changes and disjoint intervals
  have hE : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ (∀ r ∈ R, p.eval (r - ε) * p.eval (r + ε) < 0) ∧
      ∀ r ∈ R, ∀ r' ∈ R, r ≠ r' → 2 * ε < |r - r'| := by
    have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := eventually_mem_nhdsWithin
    refine hpos.and ((((Finset.eventually_all R).mpr fun r hr =>
      exists_sign_change (hroot r hr) (hderiv r hr))).and ?_)
    refine (Finset.eventually_all R).mpr fun r _ => (Finset.eventually_all R).mpr fun r' _ => ?_
    by_cases hrr : r = r'
    · exact Eventually.of_forall fun _ h => absurd hrr h
    · filter_upwards [Ioo_mem_nhdsGT (half_pos (abs_pos.mpr (sub_ne_zero.mpr hrr)))] with ε hε _
      linarith [hε.2]
  obtain ⟨ε, hε0, hεs, hεg⟩ := hE.exists
  have hev := continuous_eval_family hdeg hcont
  have hT : ∀ᶠ t in 𝓝 t₀, ∀ r ∈ R, (P t).eval (r - ε) * (P t).eval (r + ε) < 0 :=
    (Finset.eventually_all R).mpr fun r hr =>
      ((hev _).mul (hev _)).continuousAt.eventually_lt continuousAt_const (hεs r hr)
  filter_upwards [hT] with t ht
  have hroots : ∀ r ∈ R, ∃ x ∈ Ioo (r - ε) (r + ε), (P t).IsRoot x := fun r hr =>
    exists_root_Ioo_of_mul_neg (P t) (by linarith) (ht r hr)
  choose! x hx using hroots
  obtain ⟨r₀, hr₀⟩ : R.Nonempty := Finset.card_pos.mp (by omega)
  have hPt0 : P t ≠ 0 := fun h => by
    have := ht r₀ hr₀; rw [h] at this; simp at this
  have hinj : Set.InjOn x R := by
    intro r hr r' hr' hxx
    by_contra hne
    have h1 := (hx r hr).1
    have h2 := (hx r' hr').1
    rw [hxx] at h1
    rcases lt_abs.mp (hεg r hr r' hr' hne) with h | h <;>
      linarith [h1.1, h1.2, h2.1, h2.2]
  have hmaps : Set.MapsTo x R (P t).roots.toFinset := fun r hr =>
    Multiset.mem_toFinset.mpr ((mem_roots hPt0).mpr (hx r hr).2)
  have h1 := Finset.card_le_card_of_injOn x hmaps hinj
  have h2 := Multiset.toFinset_card_le (P t).roots
  have h3 := card_roots' (P t)
  have h4 := hdeg t
  exact splits_iff_card_roots.mpr (by omega)

/-- **Reality is closed** along a family whose degree is bounded and whose leading coefficient
does not vanish on `[0, 1]`. -/
theorem isClosed_splits {P : ℝ → ℝ[X]} {n : ℕ} (hdeg : ∀ t, (P t).natDegree ≤ n)
    (hcont : ∀ j, Continuous fun t => (P t).coeff j)
    (hlead : ∀ t ∈ Icc (0 : ℝ) 1, (P t).coeff n ≠ 0) :
    IsClosed (Icc (0 : ℝ) 1 ∩ {t | (P t).Splits}) := by
  refine isClosed_of_closure_subset fun t ht => ?_
  obtain ⟨s, hs, hst⟩ := mem_closure_iff_seq_limit.mp ht
  have htI : t ∈ Icc (0 : ℝ) 1 :=
    isClosed_Icc.mem_of_tendsto hst (Eventually.of_forall fun m => (hs m).1)
  refine ⟨htI, ?_⟩
  have hne : P t ≠ 0 := fun h => hlead t htI (by rw [h, coeff_zero])
  exact HTGeometry.splits_of_tendsto_coeff (qs := fun m => P (s m)) (fun m => hdeg _) (hdeg t)
    (fun m => (hs m).2) (fun j => ((hcont j).tendsto t).comp hst) hne

/-- **The exit theorem: reality leaves only through collision.** If `P 0` is real-rooted and `P 1`
is not, there is a first exit time `τ ∈ [0, 1)`: all `P s` with `0 ≤ s ≤ τ` are real-rooted, and
`P τ` has a real double root. -/
theorem exists_first_collision {P : ℝ → ℝ[X]} {n : ℕ} (hdeg : ∀ t, (P t).natDegree ≤ n)
    (hcont : ∀ j, Continuous fun t => (P t).coeff j)
    (hlead : ∀ t ∈ Icc (0 : ℝ) 1, (P t).coeff n ≠ 0) (h0 : (P 0).Splits) (h1 : ¬ (P 1).Splits) :
    ∃ τ ∈ Ico (0 : ℝ) 1, (∀ s ∈ Icc 0 τ, (P s).Splits) ∧ IsCollision (P τ) := by
  set N := {t ∈ Icc (0 : ℝ) 1 | ¬ (P t).Splits} with hN
  have hN1 : (1 : ℝ) ∈ N := ⟨⟨zero_le_one, le_rfl⟩, h1⟩
  have hNb : BddBelow N := ⟨0, fun t ht => ht.1.1⟩
  set τ := sInf N with hτ
  have hτ0 : 0 ≤ τ := le_csInf ⟨1, hN1⟩ fun t ht => ht.1.1
  have hτ1 : τ ≤ 1 := csInf_le hNb hN1
  have hbelow : ∀ s ∈ Ico 0 τ, (P s).Splits := fun s hs => by
    by_contra h
    exact absurd (csInf_le hNb ⟨⟨hs.1, by linarith [hs.2]⟩, h⟩) (not_le.mpr hs.2)
  have hτs : (P τ).Splits := by
    rcases hτ0.lt_or_eq with hpos | h
    · have hcl := isClosed_splits hdeg hcont hlead
      have hsub : Ico 0 τ ⊆ Icc (0 : ℝ) 1 ∩ {t | (P t).Splits} := fun s hs =>
        ⟨⟨hs.1, by linarith [hs.2]⟩, hbelow s hs⟩
      have hmem : τ ∈ closure (Ico 0 τ) := by
        rw [closure_Ico hpos.ne]; exact ⟨hτ0, le_rfl⟩
      exact (hcl.closure_subset_iff.mpr hsub hmem).2
    · rw [← h]; exact h0
  have hτlt : τ < 1 := lt_of_le_of_ne hτ1 fun h => h1 (h ▸ hτs)
  refine ⟨τ, ⟨hτ0, hτlt⟩, fun s hs => ?_, ?_⟩
  · rcases hs.2.lt_or_eq with h | h
    · exact hbelow s ⟨hs.1, h⟩
    · rw [h]; exact hτs
  · by_contra hc
    have hdegτ : (P τ).natDegree = n :=
      natDegree_eq_of_le_of_coeff_ne_zero (hdeg τ) (hlead τ ⟨hτ0, hτ1⟩)
    obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.mp
      (eventually_splits_of_simple hdeg hcont hτs hdegτ hc)
    have : τ + η ≤ τ := le_csInf ⟨1, hN1⟩ fun t ht => by
      by_contra hlt
      push Not at hlt
      have htτ : τ ≤ t := csInf_le hNb ht
      exact ht.2 (hball (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith))
    linarith

end GaloisForLFunctions.ZeroConfigurationGeometry
