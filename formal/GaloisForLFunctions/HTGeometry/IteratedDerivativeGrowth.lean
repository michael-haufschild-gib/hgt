import GaloisForLFunctions.HTGeometry.GoodRadiiFamily
import GaloisForLFunctions.HTGeometry.MaxModulusCharacteristicBound
import GaloisForLFunctions.HTGeometry.SmallGrowthDerivative
import GaloisForLFunctions.HTGeometry.PolynomialAntiderivative
import GaloisForLFunctions.HTGeometry.ClunieCompositionGrowth

/-!
# The characteristics of the derivatives, along a common sequence of radii

Each differentiation at most doubles the characteristic, up to the proximity of the logarithmic
derivative.  Choosing one majorant for the whole jet of `g` — and for a finite family of shifts of
`g` — gives a single sequence of radii along which all those proximities are negligible, and the
resulting bound is then self-improving: the majorant itself is at most a fixed multiple of `T(r,g)`.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Metric Real ValueDistribution MeromorphicOn Filter Set

/-- Every iterated derivative of an entire function is entire. -/
theorem differentiable_iteratedDeriv_entire {g : ℂ → ℂ} (hg : Differentiable ℂ g) (j : ℕ) :
    Differentiable ℂ (iteratedDeriv j g) := by
  induction j with
  | zero => simpa [iteratedDeriv_zero] using hg
  | succ k ih =>
      have hfan : AnalyticOnNhd ℂ (iteratedDeriv k g) Set.univ :=
        ih.differentiableOn.analyticOnNhd isOpen_univ
      intro x
      have hx := ((hfan.deriv) x (Set.mem_univ x)).differentiableAt
      simpa [iteratedDeriv_succ] using hx

/-- Every iterated derivative of an entire non-polynomial is nowhere locally zero. -/
theorem meromorphicOrderAt_iteratedDeriv_ne_top {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hgnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, g z = p.eval z) (j : ℕ) (z : ℂ) :
    meromorphicOrderAt (iteratedDeriv j g) z ≠ ⊤ := by
  intro hcon
  have hdiff : Differentiable ℂ (iteratedDeriv j g) := differentiable_iteratedDeriv_entire hg j
  have hfan : AnalyticOnNhd ℂ (iteratedDeriv j g) Set.univ :=
    hdiff.differentiableOn.analyticOnNhd isOpen_univ
  rw [meromorphicOrderAt_eq_top_iff] at hcon
  have hall := hfan.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (Set.mem_univ z) hcon.frequently
  have hzero : ∀ w : ℂ, iteratedDeriv j g w = 0 := by
    intro w
    have h := hall (Set.mem_univ w)
    simpa using h
  rcases Nat.eq_zero_or_pos j with hj | hj
  · refine hgnp ⟨0, fun w => ?_⟩
    have h := hzero w
    rw [hj, iteratedDeriv_zero] at h
    simpa using h
  · refine hgnp (exists_polynomial_of_iteratedDeriv_eq_zero hg (d := j - 1) ?_)
    intro w
    have hj' : j - 1 + 1 = j := by omega
    rw [hj']
    exact hzero w

/-- The characteristic of an entire non-polynomial tends to infinity. -/
theorem tendsto_characteristic_atTop_of_not_polynomial {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hgnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, g z = p.eval z) :
    Tendsto (fun r => characteristic g ⊤ r) atTop atTop := by
  obtain ⟨hTtop, -⟩ := charMajorant_growth_of_not_polynomial hg hgnp
  refine tendsto_atTop_mono' atTop ?_ hTtop
  filter_upwards [hTtop.eventually_gt_atTop (1 : ℝ), eventually_ge_atTop (1 : ℝ)] with r h1 hr
  have hmax : charMajorant g r = max (characteristic g ⊤ r) 1 := by
    rw [charMajorant, max_eq_left hr]
  rw [hmax] at h1 ⊢
  rcases le_or_gt (characteristic g ⊤ r) 1 with h | h
  · rw [max_eq_right h] at h1
    linarith
  · rw [max_eq_left h.le]

/-- **One sequence of radii for the whole jet and a family of shifts.**  Along it the characteristic
of every derivative up to order `n` is a fixed multiple of `T(r,g)`, and the logarithmic-derivative
proximities of `g` and of the shifts `g - b i` are negligible. -/
theorem exists_radii_jet_bound_and_error {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hgnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, g z = p.eval z) (n : ℕ) {N : ℕ} (b : Fin N → ℂ) :
    ∃ (rn : ℕ → ℝ) (C : ℝ), Tendsto rn atTop atTop ∧ 0 ≤ C ∧
      (∀ᶠ k in atTop, ∀ j ≤ n,
        characteristic (iteratedDeriv j g) ⊤ (rn k)
          ≤ 2 ^ (n + 1) * characteristic g ⊤ (rn k) + C) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
        (∑ i : Fin N, proximity (fun z => deriv g z / (g z - b i)) ⊤ (rn k))
          + proximity (fun z => deriv g z / g z) ⊤ (rn k)
          ≤ ε * characteristic g ⊤ (rn k)) := by
  classical
  have hgd : ∀ j : ℕ, Differentiable ℂ (iteratedDeriv j g) :=
    fun j => differentiable_iteratedDeriv_entire hg j
  have hgo : ∀ j : ℕ, ∀ z, meromorphicOrderAt (iteratedDeriv j g) z ≠ ⊤ :=
    fun j z => meromorphicOrderAt_iteratedDeriv_ne_top hg hgnp j z
  have hmg : Meromorphic g := fun z => (hg.analyticAt z).meromorphicAt
  -- the family
  set F : Fin (n + 1) ⊕ Fin N → ℂ → ℂ :=
    Sum.elim (fun j => iteratedDeriv (j : ℕ) g) (fun i => fun w => g w - b i) with hF
  have hFd : ∀ i, Differentiable ℂ (F i) := by
    rintro (j | i)
    · exact hgd _
    · exact hg.sub (differentiable_const _)
  have hFo : ∀ i, ∀ z, meromorphicOrderAt (F i) z ≠ ⊤ := by
    rintro (j | i) z
    · exact hgo _ z
    · exact meromorphicOrderAt_sub_const_ne_top hg hgnp (b i) z
  -- the common majorant
  set Kb : ℝ := ∑ i : Fin N, (Real.posLog ‖b i‖ + Real.log 2) with hKb
  have hKb0 : 0 ≤ Kb :=
    Finset.sum_nonneg fun i _ =>
      add_nonneg (le_max_left _ _) (Real.log_nonneg (by norm_num))
  set U : ℝ → ℝ := fun s =>
    (∑ j ∈ Finset.range (n + 1), charMajorant (iteratedDeriv j g) s) + Kb + 1 with hU
  have hUmono : Monotone U := by
    intro p q hpq
    have h : ∀ j ∈ Finset.range (n + 1),
        charMajorant (iteratedDeriv j g) p ≤ charMajorant (iteratedDeriv j g) q :=
      fun j _ => monotone_charMajorant (fun z => ((hgd j).analyticAt z).meromorphicAt) hpq
    simp only [hU]
    have := Finset.sum_le_sum h
    linarith
  have hUsum1 : ∀ s : ℝ, ((n : ℝ) + 1)
      ≤ ∑ j ∈ Finset.range (n + 1), charMajorant (iteratedDeriv j g) s := by
    intro s
    have h : ∀ j ∈ Finset.range (n + 1), (1 : ℝ) ≤ charMajorant (iteratedDeriv j g) s :=
      fun j _ => one_le_charMajorant _ s
    have := Finset.sum_le_sum h
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at this
    push_cast at this
    linarith
  have hU1 : ∀ s, 1 ≤ U s := by
    intro s
    have h := hUsum1 s
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    simp only [hU]
    linarith
  have hUdom : ∀ i, ∀ s, 1 ≤ s → characteristic (F i) ⊤ s ≤ U s := by
    rintro (j | i) s hs
    · have hle : characteristic (iteratedDeriv (j : ℕ) g) ⊤ s
          ≤ charMajorant (iteratedDeriv (j : ℕ) g) s := characteristic_le_charMajorant hs
      have hmem : (j : ℕ) ∈ Finset.range (n + 1) := Finset.mem_range.mpr j.isLt
      have hsingle : charMajorant (iteratedDeriv (j : ℕ) g) s
          ≤ ∑ jj ∈ Finset.range (n + 1), charMajorant (iteratedDeriv jj g) s :=
        Finset.single_le_sum (f := fun jj => charMajorant (iteratedDeriv jj g) s)
          (fun jj _ => le_trans zero_le_one (one_le_charMajorant _ s)) hmem
      simp only [hU, hF, Sum.elim_inl]
      linarith
    · have hshift := ValueDistribution.abs_characteristic_sub_characteristic_shift_le
        (f := g) (a₀ := b i) (r := s) hmg
      have h1 := (abs_le.mp hshift).1
      have hle : characteristic g ⊤ s ≤ charMajorant g s := characteristic_le_charMajorant hs
      have hmem : (0 : ℕ) ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
      have hsingle : charMajorant g s
          ≤ ∑ jj ∈ Finset.range (n + 1), charMajorant (iteratedDeriv jj g) s := by
        have := Finset.single_le_sum
          (f := fun jj => charMajorant (iteratedDeriv jj g) s)
          (fun jj _ => le_trans zero_le_one (one_le_charMajorant _ s)) hmem
        simpa [iteratedDeriv_zero] using this
      have hbi : Real.posLog ‖b i‖ + Real.log 2 ≤ Kb := by
        rw [hKb]
        exact Finset.single_le_sum
          (f := fun ii : Fin N => Real.posLog ‖b ii‖ + Real.log 2)
          (fun ii _ => add_nonneg (le_max_left _ _) (Real.log_nonneg (by norm_num)))
          (Finset.mem_univ i)
      simp only [hU, hF, Sum.elim_inr]
      linarith
  obtain ⟨hCMtop, hCMlog⟩ := charMajorant_growth_of_not_polynomial hg hgnp
  have hUgeCM : ∀ s : ℝ, charMajorant g s ≤ U s := by
    intro s
    have hmem : (0 : ℕ) ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    have hsingle : charMajorant g s
        ≤ ∑ jj ∈ Finset.range (n + 1), charMajorant (iteratedDeriv jj g) s := by
      have := Finset.single_le_sum
        (f := fun jj => charMajorant (iteratedDeriv jj g) s)
        (fun jj _ => le_trans zero_le_one (one_le_charMajorant _ s)) hmem
      simpa [iteratedDeriv_zero] using this
    simp only [hU]
    linarith
  have hUtop : Tendsto U atTop atTop := tendsto_atTop_mono hUgeCM hCMtop
  have hUlog : Tendsto (fun r => Real.log r / U r) atTop (nhds 0) := by
    refine squeeze_zero' ?_ ?_ hCMlog
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
      exact div_nonneg (Real.log_nonneg hr) (by linarith [hU1 r])
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
      exact div_le_div_of_nonneg_left (Real.log_nonneg hr)
        (by linarith [one_le_charMajorant g r]) (hUgeCM r)
  obtain ⟨rn, hrntop, hneg⟩ := exists_good_radii_family F hFd hFo hUmono hU1 hUdom hUlog hUtop
  set E : ℝ → ℝ := fun r => ∑ i, proximity (fun z => deriv (F i) z / F i z) ⊤ r with hEdef
  have hEnn : ∀ r, 0 ≤ E r := fun r =>
    Finset.sum_nonneg fun i _ => ValueDistribution.proximity_nonneg r
  -- one differentiation at most doubles the characteristic
  have hstep : ∀ (j : ℕ) (r : ℝ), 1 ≤ r →
      characteristic (iteratedDeriv (j + 1) g) ⊤ r
        ≤ 2 * characteristic (iteratedDeriv j g) ⊤ r
          + proximity (fun z => deriv (iteratedDeriv j g) z / iteratedDeriv j g z) ⊤ r := by
    intro j r hr
    have h := smallGrowth_characteristic_deriv_le
      (f := iteratedDeriv j g) (fun z => ((hgd j).analyticAt z).meromorphicAt) (hgo j) hr
    rw [iteratedDeriv_succ]
    exact h
  have hterm : ∀ (j : ℕ), j ≤ n → ∀ r : ℝ,
      proximity (fun z => deriv (iteratedDeriv j g) z / iteratedDeriv j g z) ⊤ r ≤ E r := by
    intro j hj r
    have hmem : (Sum.inl ⟨j, by omega⟩ : Fin (n + 1) ⊕ Fin N) ∈ Finset.univ := Finset.mem_univ _
    have h := Finset.single_le_sum
      (f := fun i : Fin (n + 1) ⊕ Fin N => proximity (fun z => deriv (F i) z / F i z) ⊤ r)
      (fun i _ => ValueDistribution.proximity_nonneg r) hmem
    simpa [hF, hEdef] using h
  -- the jet bound in terms of the error
  have hjet : ∀ (r : ℝ), 1 ≤ r → ∀ j, j ≤ n →
      characteristic (iteratedDeriv j g) ⊤ r
        ≤ 2 ^ j * characteristic g ⊤ r + (2 ^ j - 1) * E r := by
    intro r hr j
    induction j with
    | zero =>
        intro _
        simp only [iteratedDeriv_zero, pow_zero]
        have := hEnn r
        linarith
    | succ k ih =>
        intro hk
        have hprev := ih (by omega)
        have hs := hstep k r hr
        have ht := hterm k (by omega) r
        calc characteristic (iteratedDeriv (k + 1) g) ⊤ r
            ≤ 2 * characteristic (iteratedDeriv k g) ⊤ r
              + proximity (fun z => deriv (iteratedDeriv k g) z / iteratedDeriv k g z) ⊤ r := hs
          _ ≤ 2 * (2 ^ k * characteristic g ⊤ r + (2 ^ k - 1) * E r) + E r := by
              linarith
          _ = 2 ^ (k + 1) * characteristic g ⊤ r + (2 ^ (k + 1) - 1) * E r := by ring
  -- the self-improving bound for the majorant
  set C₁ : ℝ := ((n : ℝ) + 1) * 2 ^ (n + 1) with hC₁
  set C₂ : ℝ := 2 * ((n : ℝ) + 2 + Kb) with hC₂
  have hC₁pos : 0 < C₁ := by
    rw [hC₁]
    positivity
  have hUimp : ∀ r : ℝ, 1 ≤ r → E r ≤ (1 / C₁) * U r →
      U r ≤ C₁ * characteristic g ⊤ r + C₂ := by
    intro r hr hEr
    have hcm : ∀ j, j ≤ n → charMajorant (iteratedDeriv j g) r
        ≤ characteristic (iteratedDeriv j g) ⊤ r + 1 := by
      intro j hj
      have hT0 : 0 ≤ characteristic (iteratedDeriv j g) ⊤ r :=
        ValueDistribution.characteristic_nonneg hr
      have hmax : charMajorant (iteratedDeriv j g) r
          = max (characteristic (iteratedDeriv j g) ⊤ r) 1 := by
        rw [charMajorant, max_eq_left hr]
      rw [hmax]
      exact max_le (by linarith) (by linarith)
    have hsum : ∑ j ∈ Finset.range (n + 1), charMajorant (iteratedDeriv j g) r
        ≤ ((n : ℝ) + 1) * (2 ^ n * characteristic g ⊤ r + 2 ^ n * E r + 1) := by
      have hbnd : ∀ j ∈ Finset.range (n + 1),
          charMajorant (iteratedDeriv j g) r
            ≤ 2 ^ n * characteristic g ⊤ r + 2 ^ n * E r + 1 := by
        intro j hj
        have hjn : j ≤ n := by
          have := Finset.mem_range.mp hj
          omega
        have h1 := hcm j hjn
        have h2 := hjet r hr j hjn
        have hpowle : (2 : ℝ) ^ j ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hjn
        have hT0 : 0 ≤ characteristic g ⊤ r := ValueDistribution.characteristic_nonneg hr
        have hE0 := hEnn r
        nlinarith [h1, h2, hpowle, hT0, hE0]
      have h := Finset.sum_le_sum hbnd
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
      push_cast at h
      linarith
    have hUr : U r ≤ ((n : ℝ) + 1) * 2 ^ n * characteristic g ⊤ r
        + ((n : ℝ) + 1) * 2 ^ n * E r + ((n : ℝ) + 1) + Kb + 1 := by
      simp only [hU]
      nlinarith [hsum]
    have hhalf : ((n : ℝ) + 1) * 2 ^ n * E r ≤ U r / 2 := by
      have hle : E r ≤ (1 / C₁) * U r := hEr
      have hUpos : 0 < U r := by linarith [hU1 r]
      rw [hC₁] at hle
      have hstep2 : ((n : ℝ) + 1) * 2 ^ n * E r
          ≤ ((n : ℝ) + 1) * 2 ^ n * ((1 / (((n : ℝ) + 1) * 2 ^ (n + 1))) * U r) := by
        refine mul_le_mul_of_nonneg_left hle ?_
        positivity
      have heq : ((n : ℝ) + 1) * 2 ^ n * ((1 / (((n : ℝ) + 1) * 2 ^ (n + 1))) * U r) = U r / 2 := by
        have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
        have h2 : (2 : ℝ) ^ (n + 1) = 2 ^ n * 2 := by ring
        field_simp [h2]
        ring
      linarith [hstep2, heq.le]
    have hp : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by ring
    rw [hC₁, hC₂, hp]
    linarith [hUr, hhalf]
  have hC₂nn : (0 : ℝ) ≤ C₂ := by
    rw [hC₂]
    have := hKb0
    positivity
  refine ⟨rn, 2 ^ n * (C₂ / C₁), hrntop, by positivity, ?_, ?_⟩
  · filter_upwards [hneg (1 / C₁) (by positivity), hrntop.eventually_ge_atTop (1 : ℝ)]
      with k hEk hrk
    intro j hj
    have hU := hUimp (rn k) hrk hEk
    have hjetk := hjet (rn k) hrk j hj
    have hpowle : (2 : ℝ) ^ j ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hj
    have hE0 := hEnn (rn k)
    have hT0 : 0 ≤ characteristic g ⊤ (rn k) := ValueDistribution.characteristic_nonneg hrk
    have hEsmall : E (rn k) ≤ (1 / C₁) * (C₁ * characteristic g ⊤ (rn k) + C₂) := by
      refine le_trans hEk ?_
      exact mul_le_mul_of_nonneg_left hU (by positivity)
    have hC₂0 : 0 ≤ C₂ := hC₂nn
    have hinv : (1 / C₁) * (C₁ * characteristic g ⊤ (rn k) + C₂)
        = characteristic g ⊤ (rn k) + C₂ / C₁ := by
      field_simp
    rw [hinv] at hEsmall
    have hC₂C₁ : C₂ / C₁ ≤ C₂ := by
      rw [div_le_iff₀ hC₁pos]
      have hC₁1 : (1 : ℝ) ≤ C₁ := by
        rw [hC₁]
        have : (1 : ℝ) ≤ (2 : ℝ) ^ (n + 1) := one_le_pow₀ (by norm_num)
        nlinarith [Nat.cast_nonneg (α := ℝ) n]
      nlinarith [hC₂0, hC₁1]
    have hmul : (2 : ℝ) ^ n * E (rn k)
        ≤ 2 ^ n * (characteristic g ⊤ (rn k) + C₂ / C₁) :=
      mul_le_mul_of_nonneg_left hEsmall (by positivity)
    have hjmul : ((2 : ℝ) ^ j - 1) * E (rn k) ≤ 2 ^ n * E (rn k) :=
      mul_le_mul_of_nonneg_right (by linarith) hE0
    have hjT : (2 : ℝ) ^ j * characteristic g ⊤ (rn k) ≤ 2 ^ n * characteristic g ⊤ (rn k) :=
      mul_le_mul_of_nonneg_right hpowle hT0
    have hpn : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by ring
    rw [hpn]
    nlinarith [hjetk, hjmul, hjT, hmul]
  · intro ε hε
    have hTtop : Tendsto (fun k => characteristic g ⊤ (rn k)) atTop atTop :=
      (tendsto_characteristic_atTop_of_not_polynomial hg hgnp).comp hrntop
    set δ : ℝ := min (1 / C₁) (ε / (2 * C₁)) with hδ
    have hδpos : 0 < δ := by
      rw [hδ]
      exact lt_min (by positivity) (by positivity)
    filter_upwards [hneg δ hδpos, hrntop.eventually_ge_atTop (1 : ℝ),
      hTtop.eventually_ge_atTop (2 * δ * C₂ / ε)] with k hEk hrk hTk
    have hEk1 : E (rn k) ≤ (1 / C₁) * U (rn k) := by
      refine le_trans hEk ?_
      exact mul_le_mul_of_nonneg_right (min_le_left _ _) (by linarith [hU1 (rn k)])
    have hU := hUimp (rn k) hrk hEk1
    have hsum : (∑ i : Fin N, proximity (fun z => deriv g z / (g z - b i)) ⊤ (rn k))
        + proximity (fun z => deriv g z / g z) ⊤ (rn k) ≤ E (rn k) := by
      have hsplit : E (rn k)
          = (∑ j : Fin (n + 1), proximity
              (fun z => deriv (iteratedDeriv (j : ℕ) g) z / iteratedDeriv (j : ℕ) g z) ⊤ (rn k))
            + ∑ i : Fin N, proximity
              (fun z => deriv (fun w => g w - b i) z / (g z - b i)) ⊤ (rn k) := by
        simp [hEdef, hF, Fintype.sum_sum_type]
      have hzero : proximity (fun z => deriv g z / g z) ⊤ (rn k)
          ≤ ∑ j : Fin (n + 1), proximity
              (fun z => deriv (iteratedDeriv (j : ℕ) g) z / iteratedDeriv (j : ℕ) g z) ⊤ (rn k) := by
        have h := Finset.single_le_sum
          (f := fun j : Fin (n + 1) => proximity
            (fun z => deriv (iteratedDeriv (j : ℕ) g) z / iteratedDeriv (j : ℕ) g z) ⊤ (rn k))
          (fun j _ => ValueDistribution.proximity_nonneg _)
          (Finset.mem_univ (⟨0, by omega⟩ : Fin (n + 1)))
        simpa [iteratedDeriv_zero] using h
      have hshift : ∀ i : Fin N,
          proximity (fun z => deriv (fun w => g w - b i) z / (g z - b i)) ⊤ (rn k)
            = proximity (fun z => deriv g z / (g z - b i)) ⊤ (rn k) := by
        intro i
        congr 1
        funext z
        rw [deriv_sub_const]
      rw [hsplit]
      have hrw : ∑ i : Fin N, proximity
          (fun z => deriv (fun w => g w - b i) z / (g z - b i)) ⊤ (rn k)
          = ∑ i : Fin N, proximity (fun z => deriv g z / (g z - b i)) ⊤ (rn k) :=
        Finset.sum_congr rfl fun i _ => hshift i
      rw [hrw]
      linarith
    have hδC : δ ≤ ε / (2 * C₁) := min_le_right _ _
    have hUpos : 0 < U (rn k) := by linarith [hU1 (rn k)]
    have hT0 : 0 ≤ characteristic g ⊤ (rn k) := ValueDistribution.characteristic_nonneg hrk
    have hεC : δ * (C₁ * characteristic g ⊤ (rn k)) ≤ ε / 2 * characteristic g ⊤ (rn k) := by
      have : δ * C₁ ≤ ε / 2 := by
        rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * C₁)] at hδC
        linarith
      nlinarith [this, hT0]
    have hεC2 : δ * C₂ ≤ ε / 2 * characteristic g ⊤ (rn k) := by
      rw [div_le_iff₀ hε] at hTk
      linarith
    calc (∑ i : Fin N, proximity (fun z => deriv g z / (g z - b i)) ⊤ (rn k))
        + proximity (fun z => deriv g z / g z) ⊤ (rn k) ≤ E (rn k) := hsum
      _ ≤ δ * U (rn k) := hEk
      _ ≤ δ * (C₁ * characteristic g ⊤ (rn k) + C₂) :=
          mul_le_mul_of_nonneg_left hU (le_of_lt hδpos)
      _ = δ * (C₁ * characteristic g ⊤ (rn k)) + δ * C₂ := by ring
      _ ≤ ε / 2 * characteristic g ⊤ (rn k) + ε / 2 * characteristic g ⊤ (rn k) := by
          linarith
      _ = ε * characteristic g ⊤ (rn k) := by ring

end GaloisForLFunctions.HTGeometry
