import GaloisForLFunctions.PNTPlus.Consequences

/-!
# Prime counts in multiplicative windows

The prime number theorem gives `π(x) ~ x/log x`; subtracting two such asymptotics on a fixed
multiplicative window `(x, Kx]` leaves `(K−1)x/log x`, because the shift `log K` is negligible
against `log x`.  The resulting lower bound is the counting input the condensed-phase divergence
needs: on each window where the phase `τ log p` stays in the far half of its period, the primes
still carry a positive proportion of the total mass.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Asymptotics Real

theorem tendsto_atTop_const_mul {K : ℝ} (hK : 0 < K) :
    Filter.Tendsto (fun x : ℝ => K * x) Filter.atTop Filter.atTop :=
  Filter.tendsto_id.const_mul_atTop hK

/-- The prime-counting function against `x / log x`, in little-o form. -/
theorem isLittleO_primeCounting_sub :
    (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) - x / Real.log x)
      =o[atTop] (fun x : ℝ => x / Real.log x) :=
  pi_alt'.isLittleO

/-- The same, on the dilated window. -/
theorem isLittleO_primeCounting_sub_dilate {K : ℝ} (hK : 0 < K) :
    (fun x : ℝ => (Nat.primeCounting ⌊K * x⌋₊ : ℝ) - K * x / Real.log (K * x))
      =o[atTop] (fun x : ℝ => K * x / Real.log (K * x)) :=
  isLittleO_primeCounting_sub.comp_tendsto (tendsto_atTop_const_mul hK)

theorem tendsto_log_dilate_ratio {K : ℝ} (hK : 1 < K) :
    Filter.Tendsto (fun x : ℝ => Real.log x / Real.log (K * x)) atTop (nhds 1) := by
  have hKpos : (0 : ℝ) < K := lt_trans zero_lt_one hK
  have heq : (fun x : ℝ => Real.log x / Real.log (K * x))
      =ᶠ[atTop] (fun x : ℝ => 1 / (1 + Real.log K / Real.log x)) := by
    filter_upwards [eventually_gt_atTop 1, eventually_gt_atTop (0:ℝ)] with x hx1 hx0
    have hlx : 0 < Real.log x := Real.log_pos hx1
    rw [Real.log_mul (ne_of_gt hKpos) (ne_of_gt hx0)]
    field_simp
    ring
  have hzero : Filter.Tendsto (fun x : ℝ => Real.log K / Real.log x) atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds Real.tendsto_log_atTop
  have hden : Filter.Tendsto (fun x : ℝ => 1 + Real.log K / Real.log x) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hzero
  have hfrac : Filter.Tendsto (fun x : ℝ => 1 / (1 + Real.log K / Real.log x)) atTop (nhds 1) := by
    have hdiv := (tendsto_const_nhds (x := (1:ℝ)) (f := (atTop : Filter ℝ))).div hden one_ne_zero
    have hval : ((fun _ : ℝ => (1:ℝ)) / fun x : ℝ => 1 + Real.log K / Real.log x)
        = fun x : ℝ => 1 / (1 + Real.log K / Real.log x) := rfl
    rw [hval] at hdiv
    simpa using hdiv
  exact Filter.Tendsto.congr' heq.symm hfrac

theorem isBigO_dilate {K : ℝ} (hK : 1 < K) :
    (fun x : ℝ => K * x / Real.log (K * x)) =O[atTop] (fun x : ℝ => x / Real.log x) := by
  have hKpos : (0 : ℝ) < K := lt_trans zero_lt_one hK
  have hratio : Filter.Tendsto (fun x : ℝ => K * (Real.log x / Real.log (K * x)))
      atTop (nhds K) := by
    simpa using (tendsto_log_dilate_ratio hK).const_mul K
  have hbig : (fun x : ℝ => K * (Real.log x / Real.log (K * x)))
      =O[atTop] (fun _ : ℝ => (1 : ℝ)) := hratio.isBigO_one ℝ
  have heq : (fun x : ℝ => K * (Real.log x / Real.log (K * x)) * (x / Real.log x))
      =ᶠ[atTop] (fun x : ℝ => K * x / Real.log (K * x)) := by
    filter_upwards [eventually_gt_atTop 1, eventually_gt_atTop (0:ℝ)] with x hx1 hx0
    have hlx : 0 < Real.log x := Real.log_pos hx1
    have hlKx : 0 < Real.log (K * x) := by
      rw [Real.log_mul (ne_of_gt hKpos) (ne_of_gt hx0)]
      have : 0 < Real.log K := Real.log_pos hK
      linarith
    field_simp
  refine Asymptotics.IsBigO.congr' ?_ heq (Filter.Eventually.of_forall fun x => one_mul _)
  exact hbig.mul (Asymptotics.isBigO_refl (fun x : ℝ => x / Real.log x) atTop)

theorem isLittleO_dilate_sub {K : ℝ} (hK : 1 < K) :
    (fun x : ℝ => K * x / Real.log (K * x) - K * x / Real.log x)
      =o[atTop] (fun x : ℝ => x / Real.log x) := by
  have hKpos : (0 : ℝ) < K := lt_trans zero_lt_one hK
  have hzero : Filter.Tendsto (fun x : ℝ => -(K * Real.log K) / Real.log (K * x))
      atTop (nhds 0) := by
    refine Filter.Tendsto.div_atTop tendsto_const_nhds ?_
    exact Real.tendsto_log_atTop.comp (tendsto_atTop_const_mul hKpos)
  have hgo : (fun x : ℝ => -(K * Real.log K) / Real.log (K * x))
      =o[atTop] (fun _ : ℝ => (1 : ℝ)) := (Asymptotics.isLittleO_one_iff ℝ).mpr hzero
  have heq : (fun x : ℝ => -(K * Real.log K) / Real.log (K * x) * (x / Real.log x))
      =ᶠ[atTop] (fun x : ℝ => K * x / Real.log (K * x) - K * x / Real.log x) := by
    filter_upwards [eventually_gt_atTop 1, eventually_gt_atTop (0:ℝ)] with x hx1 hx0
    have hlx : 0 < Real.log x := Real.log_pos hx1
    have hlKx : 0 < Real.log (K * x) := by
      rw [Real.log_mul (ne_of_gt hKpos) (ne_of_gt hx0)]
      have : 0 < Real.log K := Real.log_pos hK
      linarith
    have hsum : Real.log (K * x) = Real.log K + Real.log x :=
      Real.log_mul (ne_of_gt hKpos) (ne_of_gt hx0)
    rw [hsum] at hlKx ⊢
    field_simp
    ring
  refine Asymptotics.IsLittleO.congr' ?_ heq (Filter.Eventually.of_forall fun x => one_mul _)
  exact hgo.mul_isBigO (Asymptotics.isBigO_refl (fun x : ℝ => x / Real.log x) atTop)

/-- **Primes in a fixed multiplicative window.**  For every `K > 1` the window `(x, Kx]` eventually
contains at least `(K−1)/2 · x/log x` primes. -/
theorem eventually_primeCount_window_ge {K : ℝ} (hK : 1 < K) :
    ∀ᶠ x : ℝ in atTop,
      (K - 1) / 2 * (x / Real.log x)
        ≤ (Nat.primeCounting ⌊K * x⌋₊ : ℝ) - (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  have hKpos : (0 : ℝ) < K := lt_trans zero_lt_one hK
  have h1 : (fun x : ℝ => (Nat.primeCounting ⌊K * x⌋₊ : ℝ) - K * x / Real.log (K * x))
      =o[atTop] (fun x : ℝ => x / Real.log x) :=
    (isLittleO_primeCounting_sub_dilate hKpos).trans_isBigO (isBigO_dilate hK)
  have h2 := isLittleO_dilate_sub hK
  have h3 := isLittleO_primeCounting_sub
  have hsum : (fun x : ℝ => (Nat.primeCounting ⌊K * x⌋₊ : ℝ) - (Nat.primeCounting ⌊x⌋₊ : ℝ)
      - (K - 1) * (x / Real.log x)) =o[atTop] (fun x : ℝ => x / Real.log x) := by
    refine ((h1.add h2).sub h3).congr' (Filter.Eventually.of_forall fun x => by ring)
      (Filter.Eventually.of_forall fun _ => rfl)
  have hbound := hsum.bound (c := (K - 1) / 2) (by linarith)
  filter_upwards [hbound, eventually_gt_atTop 1] with x hx hx1
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hxpos : 0 < x / Real.log x := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hxpos] at hx
  have habs := abs_le.mp hx
  linarith [habs.1]

/-! ## The phase windows -/

/-- **The cosine is nonpositive on the far half of each period.** -/
theorem cos_nonpos_of_mem_window {x : ℝ} (m : ℕ)
    (hlo : 2 * m * Real.pi + Real.pi / 2 ≤ x)
    (hhi : x ≤ 2 * m * Real.pi + 3 * Real.pi / 2) :
    Real.cos x ≤ 0 := by
  have hshift : Real.cos x = Real.cos (x - m * (2 * Real.pi)) := by
    have := Real.cos_add_int_mul_two_pi (x - m * (2 * Real.pi)) (m : ℤ)
    rw [← this]
    congr 1
    push_cast
    ring
  rw [hshift]
  refine Real.cos_nonpos_of_pi_div_two_le_of_le ?_ ?_
  · have : 2 * (m : ℝ) * Real.pi = (m : ℝ) * (2 * Real.pi) := by ring
    linarith [hlo, this]
  · have : 2 * (m : ℝ) * Real.pi = (m : ℝ) * (2 * Real.pi) := by ring
    linarith [hhi, this]

/-- The lower endpoint of the `m`-th phase window. -/
noncomputable def windowLo (τ : ℝ) (m : ℕ) : ℝ :=
  Real.exp ((2 * m * Real.pi + Real.pi / 2) / τ)

/-- The multiplicative width of every phase window. -/
noncomputable def windowRatio (τ : ℝ) : ℝ := Real.exp (Real.pi / τ)

theorem one_lt_windowRatio {τ : ℝ} (hτ : 0 < τ) : 1 < windowRatio τ := by
  rw [windowRatio, ← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (by positivity)

theorem windowLo_pos (τ : ℝ) (m : ℕ) : 0 < windowLo τ m := Real.exp_pos _

theorem windowRatio_mul_windowLo {τ : ℝ} (hτ : 0 < τ) (m : ℕ) :
    windowRatio τ * windowLo τ m = Real.exp ((2 * m * Real.pi + 3 * Real.pi / 2) / τ) := by
  rw [windowRatio, windowLo, ← Real.exp_add]
  congr 1
  field_simp
  ring

/-- **Every prime of the `m`-th window has nonpositive phase cosine**, hence realization defect at
least the full weight `p^{−σ}`. -/
theorem cos_nonpos_of_mem_windowRange {τ : ℝ} (hτ : 0 < τ) (m : ℕ) {y : ℝ}
    (hlo : windowLo τ m ≤ y) (hhi : y ≤ windowRatio τ * windowLo τ m) :
    Real.cos (τ * Real.log y) ≤ 0 := by
  have hypos : 0 < y := lt_of_lt_of_le (windowLo_pos τ m) hlo
  have hloglo : (2 * m * Real.pi + Real.pi / 2) / τ ≤ Real.log y := by
    have := Real.log_le_log (windowLo_pos τ m) hlo
    rwa [windowLo, Real.log_exp] at this
  have hloghi : Real.log y ≤ (2 * m * Real.pi + 3 * Real.pi / 2) / τ := by
    have := Real.log_le_log hypos hhi
    rwa [windowRatio_mul_windowLo hτ m, Real.log_exp] at this
  refine cos_nonpos_of_mem_window m ?_ ?_
  · rw [div_le_iff₀ hτ] at hloglo
    linarith [hloglo]
  · rw [le_div_iff₀ hτ] at hloghi
    linarith [hloghi]

/-! ## The window count as a finite set of primes -/

open scoped Classical in
/-- The primes of the window `(a, b]`. -/
noncomputable def primesInIoc (a b : ℕ) : Finset ℕ := (Finset.Ioc a b).filter Nat.Prime

theorem primeCounting_eq_card (n : ℕ) :
    Nat.primeCounting n = ((Finset.Iic n).filter Nat.Prime).card := by
  classical
  show Nat.count Nat.Prime (n + 1) = _
  rw [Nat.count_eq_card_filter_range, Nat.range_succ_eq_Iic]

/-- **The window count is the cardinality of the window's prime set.** -/
theorem card_primesInIoc {a b : ℕ} (hab : a ≤ b) :
    ((primesInIoc a b).card : ℝ)
      = (Nat.primeCounting b : ℝ) - (Nat.primeCounting a : ℝ) := by
  classical
  have hdisj : Disjoint ((Finset.Iic a).filter Nat.Prime) (primesInIoc a b) := by
    refine Finset.disjoint_filter_filter ?_
    exact Finset.Iic_disjoint_Ioc le_rfl
  have hunion : ((Finset.Iic a).filter Nat.Prime) ∪ primesInIoc a b
      = (Finset.Iic b).filter Nat.Prime := by
    rw [primesInIoc, ← Finset.filter_union, Finset.Iic_union_Ioc_eq_Iic hab]
  have hcard : ((Finset.Iic a).filter Nat.Prime).card + (primesInIoc a b).card
      = ((Finset.Iic b).filter Nat.Prime).card := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  rw [primeCounting_eq_card, primeCounting_eq_card, ← hcard]
  push_cast
  ring

/-- **The window's prime set sits inside the window.** -/
theorem mem_primesInIoc {a b p : ℕ} (hp : p ∈ primesInIoc a b) :
    p.Prime ∧ a < p ∧ p ≤ b := by
  classical
  rw [primesInIoc, Finset.mem_filter, Finset.mem_Ioc] at hp
  exact ⟨hp.2, hp.1.1, hp.1.2⟩

/-! ## The window in natural numbers, and its weight -/

/-- The natural lower endpoint of the `m`-th window. -/
noncomputable def winLoNat (τ : ℝ) (m : ℕ) : ℕ := ⌈windowLo τ m⌉₊

/-- The natural upper endpoint of the `m`-th window. -/
noncomputable def winHiNat (τ : ℝ) (m : ℕ) : ℕ := ⌊windowRatio τ * windowLo τ m⌋₊

theorem cos_nonpos_of_mem_winNat {τ : ℝ} (hτ : 0 < τ) (m : ℕ) {p : ℕ}
    (hp : p ∈ primesInIoc (winLoNat τ m) (winHiNat τ m)) :
    Real.cos (τ * Real.log p) ≤ 0 := by
  obtain ⟨_, hlo, hhi⟩ := mem_primesInIoc hp
  refine cos_nonpos_of_mem_windowRange hτ m ?_ ?_
  · have h1 : windowLo τ m ≤ (winLoNat τ m : ℝ) := Nat.le_ceil _
    have h2 : ((winLoNat τ m : ℕ) : ℝ) < (p : ℝ) := by exact_mod_cast hlo
    linarith
  · have hY : (0 : ℝ) ≤ windowRatio τ * windowLo τ m := by
      have h1 : (0 : ℝ) < windowRatio τ := Real.exp_pos _
      have h2 : (0 : ℝ) < windowLo τ m := windowLo_pos τ m
      positivity
    have h1 : ((winHiNat τ m : ℕ) : ℝ) ≤ windowRatio τ * windowLo τ m := Nat.floor_le hY
    have h2 : (p : ℝ) ≤ ((winHiNat τ m : ℕ) : ℝ) := by exact_mod_cast hhi
    linarith

/-- **Every prime of a window carries its full weight.**  On the window the phase cosine is
nonpositive, so `1 − cos ≥ 1`, and the smallest weight is at the right endpoint. -/
theorem window_sum_ge {σ τ : ℝ} (hσ : 0 < σ) {a b : ℕ} (hb : 0 < b)
    (hgood : ∀ p ∈ primesInIoc a b, Real.cos (τ * Real.log p) ≤ 0) :
    ((primesInIoc a b).card : ℝ) * (b : ℝ) ^ (-σ)
      ≤ ∑ p ∈ primesInIoc a b, (p : ℝ) ^ (-σ) * (1 - Real.cos (τ * Real.log p)) := by
  classical
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun p hp => ?_
  obtain ⟨hprime, _, hple⟩ := mem_primesInIoc hp
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
  have hpleR : (p : ℝ) ≤ (b : ℝ) := by exact_mod_cast hple
  have hpow : (b : ℝ) ^ (-σ) ≤ (p : ℝ) ^ (-σ) := by
    rw [Real.rpow_neg hbR.le, Real.rpow_neg hpR.le]
    refine inv_anti₀ (Real.rpow_pos_of_pos hpR _) ?_
    exact Real.rpow_le_rpow hpR.le hpleR hσ.le
  have hcos : 1 ≤ 1 - Real.cos (τ * Real.log p) := by
    have := hgood p hp
    linarith
  have hppow : (0 : ℝ) < (p : ℝ) ^ (-σ) := Real.rpow_pos_of_pos hpR _
  calc (b : ℝ) ^ (-σ) ≤ (p : ℝ) ^ (-σ) := hpow
    _ = (p : ℝ) ^ (-σ) * 1 := (mul_one _).symm
    _ ≤ (p : ℝ) ^ (-σ) * (1 - Real.cos (τ * Real.log p)) :=
        mul_le_mul_of_nonneg_left hcos hppow.le

/-! ## The windows are pairwise disjoint -/

theorem windowLo_strictMono {τ : ℝ} (hτ : 0 < τ) : StrictMono (windowLo τ) := by
  intro m n hmn
  rw [windowLo, windowLo]
  refine Real.exp_lt_exp.mpr ?_
  refine div_lt_div_of_pos_right ?_ hτ
  have hmnR : (m : ℝ) < (n : ℝ) := by exact_mod_cast hmn
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  nlinarith

theorem winHiNat_lt_winLoNat_succ {τ : ℝ} (hτ : 0 < τ) (m : ℕ) :
    winHiNat τ m < winLoNat τ (m + 1) := by
  have hlt : windowRatio τ * windowLo τ m < windowLo τ (m + 1) := by
    rw [windowRatio_mul_windowLo hτ m, windowLo]
    refine Real.exp_lt_exp.mpr ?_
    refine div_lt_div_of_pos_right ?_ hτ
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    push_cast
    nlinarith
  have hY : (0 : ℝ) ≤ windowRatio τ * windowLo τ m := by
    have h1 : (0 : ℝ) < windowRatio τ := Real.exp_pos _
    have h2 : (0 : ℝ) < windowLo τ m := windowLo_pos τ m
    positivity
  have h1 : ((winHiNat τ m : ℕ) : ℝ) ≤ windowRatio τ * windowLo τ m := Nat.floor_le hY
  have h2 : windowLo τ (m + 1) ≤ ((winLoNat τ (m + 1) : ℕ) : ℝ) := Nat.le_ceil _
  have : ((winHiNat τ m : ℕ) : ℝ) < ((winLoNat τ (m + 1) : ℕ) : ℝ) := by linarith
  exact_mod_cast this

theorem winLoNat_monotone {τ : ℝ} (hτ : 0 < τ) : Monotone (winLoNat τ) := by
  intro m n hmn
  exact Nat.ceil_le_ceil ((windowLo_strictMono hτ).monotone hmn)

theorem winHiNat_lt_winLoNat {τ : ℝ} (hτ : 0 < τ) {m n : ℕ} (hmn : m < n) :
    winHiNat τ m < winLoNat τ n :=
  lt_of_lt_of_le (winHiNat_lt_winLoNat_succ hτ m) (winLoNat_monotone hτ hmn)

/-- **The window prime sets are pairwise disjoint.** -/
theorem primesInIoc_window_disjoint {τ : ℝ} (hτ : 0 < τ) {m n : ℕ} (hmn : m ≠ n) :
    Disjoint (primesInIoc (winLoNat τ m) (winHiNat τ m))
      (primesInIoc (winLoNat τ n) (winHiNat τ n)) := by
  classical
  rcases lt_or_gt_of_ne hmn with h | h
  · refine Finset.disjoint_left.mpr fun p hp hq => ?_
    obtain ⟨_, _, hple⟩ := mem_primesInIoc hp
    obtain ⟨_, hlt, _⟩ := mem_primesInIoc hq
    exact absurd (lt_of_le_of_lt hple (lt_of_lt_of_le (winHiNat_lt_winLoNat hτ h) hlt.le))
      (lt_irrefl p)
  · refine Finset.disjoint_left.mpr fun p hp hq => ?_
    obtain ⟨_, hlt, _⟩ := mem_primesInIoc hp
    obtain ⟨_, _, hple⟩ := mem_primesInIoc hq
    exact absurd (lt_of_le_of_lt hple (lt_of_lt_of_le (winHiNat_lt_winLoNat hτ h) hlt.le))
      (lt_irrefl p)

end GaloisForLFunctions.HTGeometry
