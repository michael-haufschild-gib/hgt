import GaloisForLFunctions.HTGeometry.SignAlternationHyperbolicity

/-!
# Interlacing: a hyperbolic polynomial alternates in sign at its critical points

`SignAlternationHyperbolicity` proves that a real polynomial of degree at most `d` alternating in
sign at `d + 1` increasing points splits over `ℝ`.  This file proves the converse input that the
Jensen-section perturbation architecture needs: a **hyperbolic** polynomial of degree `n + 1` whose
derivative has `n` listed simple real roots `x 0 < … < x (n-1)`, none of which is a root of the
polynomial itself, has exactly one root in each of the `n + 1` gaps determined by those critical
points, hence its critical values **alternate in sign**, and the alternation extends past the two
outer critical points.

The proof is the elementary counting argument: off the listed critical points the derivative does
not vanish (a degree-`n+1` polynomial has at most `n` critical points), so the polynomial is
strictly monotone on each gap and therefore has at most one root there; hyperbolicity supplies
`n + 1` roots, all simple because a multiple root would be a critical point with vanishing value;
pigeonhole then places exactly one root in each gap.

## Main results

* `hyperbolic_of_sign_changes` — the sign-change form of the hyperbolicity certificate (either
  starting sign, unlike `hyperbolic_of_alternating`);
* `strictMonoOn_or_strictAntiOn_of_derivative_ne_zero` — strict monotonicity off the critical set;
* `exists_root_Ioo`, `exists_root_lt_first`, `exists_root_gt_last` — one root in every critical gap;
* `eval_mul_eval_succ_neg`, `exists_lt_first_sign_change`, `exists_gt_last_sign_change` — the
  alternation of the critical values, with the two outer sign changes.
-/

namespace GaloisForLFunctions.SignAlternation

open Polynomial Set

/-! ### Sign constancy and strict monotonicity from a nonvanishing derivative -/

/-- A polynomial without a root on an open interval keeps a constant sign there. -/
theorem sign_const_of_ne_zero_Ioo {p : ℝ[X]} {a b : ℝ}
    (h : ∀ z ∈ Ioo a b, p.eval z ≠ 0) :
    (∀ z ∈ Ioo a b, 0 < p.eval z) ∨ (∀ z ∈ Ioo a b, p.eval z < 0) := by
  by_cases hne : (Ioo a b).Nonempty
  · obtain ⟨c, hc⟩ := hne
    rcases lt_or_gt_of_ne (h c hc) with hneg | hpos
    · right
      intro z hz
      rcases lt_trichotomy z c with hlt | rfl | hgt
      · by_contra hcon
        push Not at hcon
        have hz0 : p.eval z ≠ 0 := h z hz
        have hzpos : 0 < p.eval z := lt_of_le_of_ne hcon (Ne.symm hz0)
        obtain ⟨r, hr, hroot⟩ := exists_root_of_sign_change hlt (by nlinarith)
        exact h r ⟨lt_trans hz.1 hr.1, lt_trans hr.2 hc.2⟩ hroot
      · exact hneg
      · by_contra hcon
        push Not at hcon
        have hz0 : p.eval z ≠ 0 := h z hz
        have hzpos : 0 < p.eval z := lt_of_le_of_ne hcon (Ne.symm hz0)
        obtain ⟨r, hr, hroot⟩ := exists_root_of_sign_change hgt (by nlinarith)
        exact h r ⟨lt_trans hc.1 hr.1, lt_trans hr.2 hz.2⟩ hroot
    · left
      intro z hz
      rcases lt_trichotomy z c with hlt | rfl | hgt
      · by_contra hcon
        push Not at hcon
        have hz0 : p.eval z ≠ 0 := h z hz
        have hzneg : p.eval z < 0 := lt_of_le_of_ne hcon hz0
        obtain ⟨r, hr, hroot⟩ := exists_root_of_sign_change hlt (by nlinarith)
        exact h r ⟨lt_trans hz.1 hr.1, lt_trans hr.2 hc.2⟩ hroot
      · exact hpos
      · by_contra hcon
        push Not at hcon
        have hz0 : p.eval z ≠ 0 := h z hz
        have hzneg : p.eval z < 0 := lt_of_le_of_ne hcon hz0
        obtain ⟨r, hr, hroot⟩ := exists_root_of_sign_change hgt (by nlinarith)
        exact h r ⟨lt_trans hc.1 hr.1, lt_trans hr.2 hz.2⟩ hroot
  · left
    intro z hz
    exact absurd ⟨z, hz⟩ hne

/-- A polynomial whose derivative does not vanish on an open interval is strictly monotone on the
closed interval. -/
theorem strictMonoOn_or_strictAntiOn_of_derivative_ne_zero {p : ℝ[X]} {a b : ℝ}
    (h : ∀ z ∈ Ioo a b, p.derivative.eval z ≠ 0) :
    StrictMonoOn (fun z => p.eval z) (Icc a b) ∨ StrictAntiOn (fun z => p.eval z) (Icc a b) := by
  have hcont : ContinuousOn (fun z => p.eval z) (Icc a b) := (p.continuous_aeval).continuousOn
  have hderiv : ∀ z, deriv (fun z => p.eval z) z = p.derivative.eval z := fun z =>
    (p.hasDerivAt z).deriv
  rcases sign_const_of_ne_zero_Ioo (p := p.derivative) h with hpos | hneg
  · left
    refine strictMonoOn_of_deriv_pos (convex_Icc a b) hcont (fun z hz => ?_)
    rw [interior_Icc] at hz
    rw [hderiv]
    exact hpos z hz
  · right
    refine strictAntiOn_of_deriv_neg (convex_Icc a b) hcont (fun z hz => ?_)
    rw [interior_Icc] at hz
    rw [hderiv]
    exact hneg z hz

/-- A strictly monotone (or antitone) function with an interior zero has endpoint values of
opposite sign. -/
theorem eval_mul_eval_neg_of_root_mem_Ioo {p : ℝ[X]} {a b r : ℝ}
    (hmono : StrictMonoOn (fun z => p.eval z) (Icc a b) ∨
      StrictAntiOn (fun z => p.eval z) (Icc a b))
    (hr : r ∈ Ioo a b) (hroot : p.eval r = 0) :
    p.eval a * p.eval b < 0 := by
  have hab : a < b := lt_trans hr.1 hr.2
  have hma : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hmb : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  have hmr : r ∈ Icc a b := ⟨hr.1.le, hr.2.le⟩
  rcases hmono with hmono | hanti
  · have h1 : p.eval a < p.eval r := hmono hma hmr hr.1
    have h2 : p.eval r < p.eval b := hmono hmr hmb hr.2
    rw [hroot] at h1 h2
    nlinarith
  · have h1 : p.eval r < p.eval a := hanti hma hmr hr.1
    have h2 : p.eval b < p.eval r := hanti hmr hmb hr.2
    rw [hroot] at h1 h2
    nlinarith

/-! ### Consecutive sign changes certify hyperbolicity -/

theorem hyperbolic_neg_iff {p : ℝ[X]} : Hyperbolic (-p) ↔ Hyperbolic p := by
  unfold Hyperbolic
  rw [Polynomial.roots_neg, Polynomial.natDegree_neg]

/-- **Consecutive sign changes certify hyperbolicity.**  A polynomial of degree at most `d` whose
values at `d + 1` increasing points change sign at every step splits over `ℝ`. -/
theorem hyperbolic_of_sign_changes {p : ℝ[X]} {d : ℕ} {y : ℕ → ℝ}
    (hdeg : p.natDegree ≤ d)
    (hy : ∀ i, i < d → y i < y (i + 1))
    (hchange : ∀ i, i < d → p.eval (y i) * p.eval (y (i + 1)) < 0) :
    Hyperbolic p := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have h1 : p.roots.card ≤ p.natDegree := Polynomial.card_roots' p
    unfold Hyperbolic
    omega
  have hne : ∀ i, i ≤ d → p.eval (y i) ≠ 0 := by
    intro i hi h
    rcases Nat.lt_or_ge i d with hlt | hge
    · have hc := hchange i hlt
      rw [h, zero_mul] at hc
      exact lt_irrefl 0 hc
    · have hid : i = d := le_antisymm hi hge
      have hc := hchange (d - 1) (by omega)
      rw [show d - 1 + 1 = d by omega, ← hid, h, mul_zero] at hc
      exact lt_irrefl 0 hc
  rcases lt_or_gt_of_ne (hne 0 (Nat.zero_le _)) with hneg | hpos
  · rw [← hyperbolic_neg_iff]
    refine hyperbolic_of_alternating (d := d) (y := y) (by simpa using hdeg) hy ?_
    intro i hi
    induction i with
    | zero => simpa using hneg
    | succ k ih =>
        have hk : k < d := by omega
        have hprev := ih (le_of_lt hk)
        have hc := hchange k hk
        simp only [Polynomial.eval_neg] at hprev ⊢
        rcases Nat.even_or_odd k with he | ho
        · rw [he.neg_one_pow, one_mul] at hprev
          rw [(Even.add_one he).neg_one_pow]
          nlinarith
        · rw [ho.neg_one_pow] at hprev
          rw [(Odd.add_one ho).neg_one_pow, one_mul]
          nlinarith
  · refine hyperbolic_of_alternating (d := d) (y := y) hdeg hy ?_
    intro i hi
    induction i with
    | zero => simpa using hpos
    | succ k ih =>
        have hk : k < d := by omega
        have hprev := ih (le_of_lt hk)
        have hc := hchange k hk
        rcases Nat.even_or_odd k with he | ho
        · rw [he.neg_one_pow, one_mul] at hprev
          rw [(Even.add_one he).neg_one_pow]
          nlinarith
        · rw [ho.neg_one_pow] at hprev
          rw [(Odd.add_one ho).neg_one_pow, one_mul]
          nlinarith

/-! ### Interlacing: a hyperbolic polynomial has one root in every critical gap -/

section Interlacing

open Classical in
/-- The number of listed critical points lying strictly below `z`. -/
noncomputable def critBelow (n : ℕ) (x : ℕ → ℝ) (z : ℝ) : ℕ :=
  ((Finset.range n).filter (fun j => x j < z)).card

theorem critBelow_le (n : ℕ) (x : ℕ → ℝ) (z : ℝ) : critBelow n x z ≤ n := by
  classical
  simpa [critBelow] using Finset.card_filter_le (Finset.range n) (fun j => x j < z)

variable {C : ℝ[X]} {n : ℕ} {x : ℕ → ℝ}

theorem ne_zero_of_natDegree_eq_succ (hdeg : C.natDegree = n + 1) : C ≠ 0 := by
  intro h
  rw [h] at hdeg
  simp at hdeg

theorem derivative_ne_zero_of_natDegree_eq_succ (hdeg : C.natDegree = n + 1) :
    C.derivative ≠ 0 := by
  intro h
  rw [Polynomial.eq_C_of_derivative_eq_zero h] at hdeg
  simp at hdeg

/-- **The listed critical points are all of them.**  A degree-`n+1` polynomial has at most `n`
critical points, so `n` distinct listed ones exhaust the roots of the derivative. -/
theorem critical_mem_of_derivative_eq_zero (hdeg : C.natDegree = n + 1)
    (hxmono : ∀ i j, i < j → j < n → x i < x j)
    (hcrit : ∀ i, i < n → C.derivative.eval (x i) = 0)
    {z : ℝ} (hz : C.derivative.eval z = 0) : ∃ i, i < n ∧ z = x i := by
  classical
  by_contra hcon
  push Not at hcon
  have hC'0 : C.derivative ≠ 0 := derivative_ne_zero_of_natDegree_eq_succ hdeg
  have hinj : Set.InjOn x (Finset.range n) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact absurd hij (ne_of_lt (hxmono i j h hj))
    · exact absurd hij.symm (ne_of_lt (hxmono j i h hi))
  have hTcard : ((Finset.range n).image x).card = n := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hTsub : (Finset.range n).image x ⊆ C.derivative.roots.toFinset := by
    intro t ht
    rw [Finset.mem_image] at ht
    obtain ⟨i, hi, rfl⟩ := ht
    rw [Finset.mem_range] at hi
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hC'0).mpr (hcrit i hi))
  have hzmem : z ∈ C.derivative.roots.toFinset :=
    Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hC'0).mpr hz)
  have hznot : z ∉ (Finset.range n).image x := by
    rw [Finset.mem_image]
    rintro ⟨i, hi, hxi⟩
    rw [Finset.mem_range] at hi
    exact hcon i hi hxi.symm
  have hins : insert z ((Finset.range n).image x) ⊆ C.derivative.roots.toFinset :=
    Finset.insert_subset hzmem hTsub
  have h1 : (insert z ((Finset.range n).image x)).card = n + 1 := by
    rw [Finset.card_insert_of_notMem hznot, hTcard]
  have h2 : C.derivative.roots.toFinset.card ≤ n := by
    calc C.derivative.roots.toFinset.card ≤ Multiset.card C.derivative.roots :=
          Multiset.toFinset_card_le _
      _ ≤ C.derivative.natDegree := Polynomial.card_roots' _
      _ ≤ C.natDegree - 1 := Polynomial.natDegree_derivative_le C
      _ = n := by omega
  have h3 := Finset.card_le_card hins
  omega

/-- Off the listed critical points the derivative does not vanish. -/
theorem derivative_ne_zero_of_notMem (hdeg : C.natDegree = n + 1)
    (hxmono : ∀ i j, i < j → j < n → x i < x j)
    (hcrit : ∀ i, i < n → C.derivative.eval (x i) = 0)
    {z : ℝ} (hz : ∀ i, i < n → z ≠ x i) : C.derivative.eval z ≠ 0 := by
  intro h
  obtain ⟨i, hi, hzx⟩ := critical_mem_of_derivative_eq_zero hdeg hxmono hcrit h
  exact hz i hi hzx

/-- **All roots are simple.**  A multiple root would be a critical point with vanishing value. -/
theorem roots_toFinset_card_eq (hdeg : C.natDegree = n + 1) (hhyp : Hyperbolic C)
    (hxmono : ∀ i j, i < j → j < n → x i < x j)
    (hcrit : ∀ i, i < n → C.derivative.eval (x i) = 0)
    (hxne : ∀ i, i < n → C.eval (x i) ≠ 0) :
    C.roots.toFinset.card = n + 1 := by
  classical
  have hC0 : C ≠ 0 := ne_zero_of_natDegree_eq_succ hdeg
  have hnodup : C.roots.Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro a
    by_contra hcon
    push Not at hcon
    have hmult : 1 < C.rootMultiplicity a := by rwa [Polynomial.count_roots] at hcon
    have hroot' : C.derivative.eval a = 0 := by
      have h := Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity
        (p := C) (t := a) (n := 1) hmult
      simpa [Polynomial.IsRoot] using h
    obtain ⟨i, hi, rfl⟩ := critical_mem_of_derivative_eq_zero hdeg hxmono hcrit hroot'
    exact hxne i hi ((Polynomial.rootMultiplicity_pos hC0).mp (by omega))
  rw [Multiset.toFinset_card_of_nodup hnodup, hhyp, hdeg]

theorem index_lt_of_eval_lt (hxmono : ∀ i j, i < j → j < n → x i < x j)
    {i j : ℕ} (hi : i < n) (h : x i < x j) : i < j := by
  by_contra hcon
  push Not at hcon
  rcases eq_or_lt_of_le hcon with rfl | hlt
  · exact lt_irrefl _ h
  · exact absurd h (not_lt.mpr (le_of_lt (hxmono j i hlt hi)))

/-- Two distinct roots cannot share a critical gap. -/
theorem eq_of_critBelow_eq (hdeg : C.natDegree = n + 1)
    (hxmono : ∀ i j, i < j → j < n → x i < x j)
    (hcrit : ∀ i, i < n → C.derivative.eval (x i) = 0)
    (hxne : ∀ i, i < n → C.eval (x i) ≠ 0)
    {z₁ z₂ : ℝ} (h1 : C.eval z₁ = 0) (h2 : C.eval z₂ = 0)
    (heq : critBelow n x z₁ = critBelow n x z₂) : z₁ = z₂ := by
  have key : ∀ w₁ w₂ : ℝ, C.eval w₁ = 0 → C.eval w₂ = 0 →
      critBelow n x w₁ = critBelow n x w₂ → w₁ < w₂ → False := by
    intro w₁ w₂ hw1 hw2 hweq hlt
    have hsub : (Finset.range n).filter (fun j => x j < w₁)
        ⊆ (Finset.range n).filter (fun j => x j < w₂) := by
      intro j hj
      rw [Finset.mem_filter] at hj ⊢
      exact ⟨hj.1, lt_trans hj.2 hlt⟩
    have hfeq : (Finset.range n).filter (fun j => x j < w₁)
        = (Finset.range n).filter (fun j => x j < w₂) :=
      Finset.eq_of_subset_of_card_le hsub (le_of_eq hweq.symm)
    have hno : ∀ j, j < n → ¬ (w₁ ≤ x j ∧ x j ≤ w₂) := by
      rintro j hj ⟨hj1, hj2⟩
      have hne2 : x j ≠ w₂ := fun h => hxne j hj (by rw [h, hw2])
      have hmem : j ∈ (Finset.range n).filter (fun j => x j < w₂) :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, lt_of_le_of_ne hj2 hne2⟩
      rw [← hfeq, Finset.mem_filter] at hmem
      exact absurd hmem.2 (not_lt.mpr hj1)
    have hderiv : ∀ w ∈ Set.Ioo w₁ w₂, C.derivative.eval w ≠ 0 := by
      intro w hw
      refine derivative_ne_zero_of_notMem hdeg hxmono hcrit ?_
      intro i hi hwx
      exact hno i hi ⟨le_of_lt (hwx ▸ hw.1), le_of_lt (hwx ▸ hw.2)⟩
    rcases strictMonoOn_or_strictAntiOn_of_derivative_ne_zero hderiv with hm | ha
    · have hcmp := hm (⟨le_rfl, hlt.le⟩ : w₁ ∈ Set.Icc w₁ w₂)
        (⟨hlt.le, le_rfl⟩ : w₂ ∈ Set.Icc w₁ w₂) hlt
      simp only [hw1, hw2] at hcmp
      exact lt_irrefl 0 hcmp
    · have hcmp := ha (⟨le_rfl, hlt.le⟩ : w₁ ∈ Set.Icc w₁ w₂)
        (⟨hlt.le, le_rfl⟩ : w₂ ∈ Set.Icc w₁ w₂) hlt
      simp only [hw1, hw2] at hcmp
      exact lt_irrefl 0 hcmp
  rcases lt_trichotomy z₁ z₂ with hlt | heqz | hgt
  · exact absurd (key z₁ z₂ h1 h2 heq hlt) not_false
  · exact heqz
  · exact absurd (key z₂ z₁ h2 h1 heq.symm hgt) not_false

/-- **Exactly one root per critical gap.**  Every gap index between `0` and `n` is realised. -/
theorem exists_root_critBelow_eq (hdeg : C.natDegree = n + 1) (hhyp : Hyperbolic C)
    (hxmono : ∀ i j, i < j → j < n → x i < x j)
    (hcrit : ∀ i, i < n → C.derivative.eval (x i) = 0)
    (hxne : ∀ i, i < n → C.eval (x i) ≠ 0)
    {k : ℕ} (hk : k ≤ n) : ∃ r, C.eval r = 0 ∧ critBelow n x r = k := by
  have hC0 : C ≠ 0 := ne_zero_of_natDegree_eq_succ hdeg
  have hcard : C.roots.toFinset.card = n + 1 := roots_toFinset_card_eq hdeg hhyp hxmono hcrit hxne
  have hinj : Set.InjOn (critBelow n x) (C.roots.toFinset : Set ℝ) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, Multiset.mem_toFinset] at ha hb
    exact eq_of_critBelow_eq hdeg hxmono hcrit hxne
      ((Polynomial.mem_roots hC0).mp ha) ((Polynomial.mem_roots hC0).mp hb) hab
  have himg : C.roots.toFinset.image (critBelow n x) ⊆ Finset.range (n + 1) := by
    intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨r, _, hrm⟩ := hm
    exact Finset.mem_range.mpr (by rw [← hrm]; exact Nat.lt_succ_of_le (critBelow_le n x r))
  have hcard2 : (C.roots.toFinset.image (critBelow n x)).card = n + 1 := by
    rw [Finset.card_image_of_injOn hinj, hcard]
  have heqimg : C.roots.toFinset.image (critBelow n x) = Finset.range (n + 1) :=
    Finset.eq_of_subset_of_card_le himg (by rw [hcard2, Finset.card_range])
  have hmem : k ∈ C.roots.toFinset.image (critBelow n x) := by
    rw [heqimg]
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
  rw [Finset.mem_image] at hmem
  obtain ⟨r, hr, hrk⟩ := hmem
  exact ⟨r, (Polynomial.mem_roots hC0).mp (Multiset.mem_toFinset.mp hr), hrk⟩

/-- A root lies strictly inside every gap between consecutive critical points. -/
theorem exists_root_Ioo (hdeg : C.natDegree = n + 1) (hhyp : Hyperbolic C)
    (hxmono : ∀ i j, i < j → j < n → x i < x j)
    (hcrit : ∀ i, i < n → C.derivative.eval (x i) = 0)
    (hxne : ∀ i, i < n → C.eval (x i) ≠ 0)
    {i : ℕ} (hi : i + 1 < n) : ∃ r ∈ Set.Ioo (x i) (x (i + 1)), C.eval r = 0 := by
  obtain ⟨r, hr0, hrk⟩ :=
    exists_root_critBelow_eq hdeg hhyp hxmono hcrit hxne (k := i + 1) (by omega)
  refine ⟨r, ⟨?_, ?_⟩, hr0⟩
  · by_contra hcon
    push Not at hcon
    have hsub : (Finset.range n).filter (fun j => x j < r) ⊆ Finset.range i := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_range] at hj
      rw [Finset.mem_range]
      by_contra hji
      push Not at hji
      rcases eq_or_lt_of_le hji with h | h
      · rw [← h] at hj
        exact absurd hj.2 (not_lt.mpr hcon)
      · exact absurd hj.2 (not_lt.mpr (le_trans hcon (le_of_lt (hxmono i j h hj.1))))
    have hcle := Finset.card_le_card hsub
    rw [Finset.card_range] at hcle
    simp only [critBelow] at hrk
    omega
  · by_contra hcon
    push Not at hcon
    have hnex : x (i + 1) ≠ r := fun h => hxne (i + 1) (by omega) (by rw [h, hr0])
    have hlt : x (i + 1) < r := lt_of_le_of_ne hcon hnex
    have hsub : Finset.range (i + 2) ⊆ (Finset.range n).filter (fun j => x j < r) := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hj) with h | h
      · rw [h]; exact hlt
      · exact lt_trans (hxmono j (i + 1) h (by omega)) hlt
    have hcle := Finset.card_le_card hsub
    rw [Finset.card_range] at hcle
    simp only [critBelow] at hrk
    omega

/-- A root lies strictly below the first critical point. -/
theorem exists_root_lt_first (hdeg : C.natDegree = n + 1) (hhyp : Hyperbolic C)
    (hxmono : ∀ i j, i < j → j < n → x i < x j)
    (hcrit : ∀ i, i < n → C.derivative.eval (x i) = 0)
    (hxne : ∀ i, i < n → C.eval (x i) ≠ 0)
    (hn : 0 < n) : ∃ r, r < x 0 ∧ C.eval r = 0 := by
  obtain ⟨r, hr0, hrk⟩ :=
    exists_root_critBelow_eq hdeg hhyp hxmono hcrit hxne (k := 0) (Nat.zero_le _)
  refine ⟨r, ?_, hr0⟩
  have hnex : x 0 ≠ r := fun h => hxne 0 hn (by rw [h, hr0])
  rcases lt_trichotomy r (x 0) with h | h | h
  · exact h
  · exact absurd h.symm hnex
  · exfalso
    have hmem : (0 : ℕ) ∈ (Finset.range n).filter (fun j => x j < r) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hn, h⟩
    simp only [critBelow] at hrk
    rw [Finset.card_eq_zero] at hrk
    rw [hrk] at hmem
    exact absurd hmem (Finset.notMem_empty 0)

/-- A root lies strictly above the last critical point. -/
theorem exists_root_gt_last (hdeg : C.natDegree = n + 1) (hhyp : Hyperbolic C)
    (hxmono : ∀ i j, i < j → j < n → x i < x j)
    (hcrit : ∀ i, i < n → C.derivative.eval (x i) = 0)
    (hxne : ∀ i, i < n → C.eval (x i) ≠ 0)
    (hn : 0 < n) : ∃ r, x (n - 1) < r ∧ C.eval r = 0 := by
  obtain ⟨r, hr0, hrk⟩ :=
    exists_root_critBelow_eq hdeg hhyp hxmono hcrit hxne (k := n) le_rfl
  refine ⟨r, ?_, hr0⟩
  by_contra hcon
  push Not at hcon
  have hnex : x (n - 1) ≠ r := fun h => hxne (n - 1) (by omega) (by rw [h, hr0])
  have hlt : r < x (n - 1) := lt_of_le_of_ne hcon (Ne.symm hnex)
  have hsub : (Finset.range n).filter (fun j => x j < r) ⊆ Finset.range (n - 1) := by
    intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    rw [Finset.mem_range]
    by_contra hji
    push Not at hji
    have hjn : j = n - 1 := by omega
    rw [hjn] at hj
    exact absurd hj.2 (not_lt.mpr hlt.le)
  have hcle := Finset.card_le_card hsub
  rw [Finset.card_range] at hcle
  simp only [critBelow] at hrk
  omega

/-! ### Alternation of the critical values -/

/-- **The critical values of a hyperbolic polynomial alternate in sign.** -/
theorem eval_mul_eval_succ_neg (hdeg : C.natDegree = n + 1) (hhyp : Hyperbolic C)
    (hxmono : ∀ i j, i < j → j < n → x i < x j)
    (hcrit : ∀ i, i < n → C.derivative.eval (x i) = 0)
    (hxne : ∀ i, i < n → C.eval (x i) ≠ 0)
    {i : ℕ} (hi : i + 1 < n) : C.eval (x i) * C.eval (x (i + 1)) < 0 := by
  obtain ⟨r, hr, hr0⟩ := exists_root_Ioo hdeg hhyp hxmono hcrit hxne hi
  refine eval_mul_eval_neg_of_root_mem_Ioo ?_ hr hr0
  refine strictMonoOn_or_strictAntiOn_of_derivative_ne_zero ?_
  intro w hw
  refine derivative_ne_zero_of_notMem hdeg hxmono hcrit ?_
  intro j hj hwx
  subst hwx
  have h1 : i < j := index_lt_of_eval_lt hxmono (by omega) hw.1
  have h2 : j < i + 1 := index_lt_of_eval_lt hxmono hj hw.2
  omega

/-- A sign change to the left of the first critical point. -/
theorem exists_lt_first_sign_change (hdeg : C.natDegree = n + 1) (hhyp : Hyperbolic C)
    (hxmono : ∀ i j, i < j → j < n → x i < x j)
    (hcrit : ∀ i, i < n → C.derivative.eval (x i) = 0)
    (hxne : ∀ i, i < n → C.eval (x i) ≠ 0)
    (hn : 0 < n) : ∃ y₀, y₀ < x 0 ∧ C.eval y₀ * C.eval (x 0) < 0 := by
  obtain ⟨r, hr, hr0⟩ := exists_root_lt_first hdeg hhyp hxmono hcrit hxne hn
  refine ⟨r - 1, by linarith, ?_⟩
  refine eval_mul_eval_neg_of_root_mem_Ioo ?_ ⟨by linarith, hr⟩ hr0
  refine strictMonoOn_or_strictAntiOn_of_derivative_ne_zero ?_
  intro w hw
  refine derivative_ne_zero_of_notMem hdeg hxmono hcrit ?_
  intro j hj hwx
  subst hwx
  have := index_lt_of_eval_lt hxmono hj hw.2
  omega

/-- A sign change to the right of the last critical point. -/
theorem exists_gt_last_sign_change (hdeg : C.natDegree = n + 1) (hhyp : Hyperbolic C)
    (hxmono : ∀ i j, i < j → j < n → x i < x j)
    (hcrit : ∀ i, i < n → C.derivative.eval (x i) = 0)
    (hxne : ∀ i, i < n → C.eval (x i) ≠ 0)
    (hn : 0 < n) : ∃ y₁, x (n - 1) < y₁ ∧ C.eval (x (n - 1)) * C.eval y₁ < 0 := by
  obtain ⟨r, hr, hr0⟩ := exists_root_gt_last hdeg hhyp hxmono hcrit hxne hn
  refine ⟨r + 1, by linarith, ?_⟩
  refine eval_mul_eval_neg_of_root_mem_Ioo ?_ ⟨hr, by linarith⟩ hr0
  refine strictMonoOn_or_strictAntiOn_of_derivative_ne_zero ?_
  intro w hw
  refine derivative_ne_zero_of_notMem hdeg hxmono hcrit ?_
  intro j hj hwx
  subst hwx
  have := index_lt_of_eval_lt hxmono (show n - 1 < n by omega) hw.1
  omega

end Interlacing

end GaloisForLFunctions.SignAlternation
