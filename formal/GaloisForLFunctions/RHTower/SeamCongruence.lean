/-
The seam congruence exhausted (doc 79; task #27): the hL input of the window
relation, worked to its structural floor.

Two theorems close the topic's shape:

* `seam_iff_rung` / `anneal_seam_iff_rung_of_domination` — **the blindness
  identity**: given the two window identities D = L + 2N and the deck-side
  congruence (supplied by domination as exact equality), the seam congruence
  hL at level 2^(k+1) is EQUIVALENT to the rung congruence at 2^k. Doc 76 §1's
  structural blindness, machine-checked as an equivalence: the seam datum is
  not an auxiliary input sourceable from a side channel — it IS the rung
  statement in on-line coordinates. There is no seam-side shortcut; the value
  of the seam is the change of coordinates (2D off-line counting → 1D on-line
  counting), where the finite carrier is certifiable and ξ is REAL.

* `window_online_of_sign_data` and its consumers — **the discharge
  instrument**: ξ is real on the critical line (`xi_im_eq_zero_on_line`), so
  s certified sign alternations along the window segment produce s distinct
  on-line zeros (intermediate value, no argument principle); if the total
  enclosed count is ≤ s (domination + certified finite side), the on-line sum
  EQUALS the total and the right-half sum is ZERO. Turing's counting core,
  welded to the finite carrier through the Rouché substitute — every
  hypothesis is finite certifiable data (rational sign points, box bounds).

The D–H filter is respected: for the Davenport–Heilbronn analogue the same
identities and instruments hold VERBATIM — and the sign-change count there
falls short of the enclosed total exactly on windows containing its off-line
zeros, so the instrument (correctly) refuses to fire. Discrimination stays at
(XLD) + budget, where doc 75 located it.
-/
import GaloisForLFunctions.RHTower.AnnealWindowRelation
import GaloisForLFunctions.RHTower.DictionarySign
import GaloisForLFunctions.RHTower.EMCarrier

namespace RHTower

open Complex Metric

/-! ### §1 The blindness identity: seam congruence ⟺ rung congruence -/

/-- **The blindness identity, arithmetic core.** Under the two window
identities and the deck congruence at level `2^(k+1)`, the seam congruence at
`2^(k+1)` is EQUIVALENT to the rung congruence at `2^k`. Forward is
`window_N_congruence`; backward says the seam datum carries no more and no
less than the rung. -/
theorem seam_iff_rung {k D₁ L₁ N₁ D₂ L₂ N₂ : ℕ}
    (hID₁ : D₁ = L₁ + 2 * N₁) (hID₂ : D₂ = L₂ + 2 * N₂)
    (hD : D₁ ≡ D₂ [MOD 2 ^ (k + 1)]) :
    (L₁ ≡ L₂ [MOD 2 ^ (k + 1)]) ↔ (N₁ ≡ N₂ [MOD 2 ^ k]) := by
  constructor
  · intro hL
    exact window_N_congruence hID₁ hID₂ hD hL
  · intro hN
    have h2 : 2 * N₁ ≡ 2 * N₂ [MOD 2 ^ (k + 1)] := by
      have h := Nat.ModEq.mul_left' (c := 2) hN
      have hpow : 2 * 2 ^ k = 2 ^ (k + 1) := by
        rw [pow_succ]
        ring
      rwa [hpow] at h
    subst hID₁
    subst hID₂
    exact Nat.ModEq.add_right_cancel h2 hD

/-- **The blindness identity on the carriers, under domination.** With the
deck side discharged by domination (exact D-equality via the Rouché
substitute), the seam congruence hL at `2^(k+1)` is EQUIVALENT to the rung
congruence at `2^k` — for every window and every rung. Proving hL IS proving
the rung; the seam contributes a change of coordinates, not a new input. -/
theorem anneal_seam_iff_rung_of_domination {N : ℕ} (k : ℕ)
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ} {h h' : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hstrip : ∀ z ∈ t₂, 0 < z.re ∧ z.re < 1)
    (hm₂ : ∀ z ∈ t₂, (m₂ z : ℕ∞) = analyticOrderAt (completedGN N) z)
    (hcl₂ : ∀ z ∈ t₂, lineReflect z ∈ t₂)
    (hρ₁ : ∀ w ∈ t₁, ‖w - a‖ ≤ r₀) (hρ₂ : ∀ w ∈ t₂, ‖w - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball a R)) (hh0' : ∀ z ∈ ball a R, h' z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    (hfact₂ : ∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h' z)
    (hdom : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖xi z - completedGN N z‖ < ‖completedGN N z‖) :
    (∑ z ∈ t₁.filter (fun z => z.re = 1 / 2), m₁ z
        ≡ ∑ z ∈ t₂.filter (fun z => z.re = 1 / 2), m₂ z [MOD 2 ^ (k + 1)]) ↔
      (∑ z ∈ t₁.filter (fun z => 1 / 2 < z.re), m₁ z
        ≡ ∑ z ∈ t₂.filter (fun z => 1 / 2 < z.re), m₂ z [MOD 2 ^ k]) := by
  have hDeq : ∑ w ∈ t₁, m₁ w = ∑ w ∈ t₂, m₂ w :=
    anneal_D_transport h0 hrR hρ₁ hρ₂ hh hh0 hh' hh0' hfact₁ hfact₂ hdom
  have hmr₁ : ∀ z ∈ t₁, m₁ (lineReflect z) = m₁ z := by
    intro z hz
    have h1 := xi_orderAt_lineReflect z
    have h2 := hm₁ _ (hcl₁ z hz)
    rw [h1, ← hm₁ z hz] at h2
    exact Nat.cast_inj.mp h2
  have hmr₂ : ∀ z ∈ t₂, m₂ (lineReflect z) = m₂ z := by
    intro z hz
    obtain ⟨hz0, hz1⟩ := hstrip z hz
    have h1eq := completedGN_orderAt_lineReflect (N := N) hz0 hz1
    have h2 := hm₂ _ (hcl₂ z hz)
    rw [h1eq, ← hm₂ z hz] at h2
    exact Nat.cast_inj.mp h2
  exact seam_iff_rung (window_identity hcl₁ hmr₁) (window_identity hcl₂ hmr₂)
    (hDeq ▸ Nat.ModEq.refl _)

/-- Congruence at every 2-power level is equality. -/
theorem eq_of_forall_two_pow_modEq {a b : ℕ} (h : ∀ k, a ≡ b [MOD 2 ^ k]) :
    a = b := by
  have h2 : a + b < 2 ^ (a + b + 1) :=
    Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hmod := h (a + b + 1)
  unfold Nat.ModEq at hmod
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod
  exact hmod

/-- **Tower limit of the seam column.** The seam congruence at EVERY level
`2^(k+1)` is exactly the off-line count matching `N₁ = N₂`: the seam column,
climbed to the top, carries the full matching and nothing besides. The
generative work therefore moves entirely into per-window production of the
matching data — sign alternations and finite-side certificates — which the
instruments below supply. -/
theorem seam_tower_iff_offline_eq {D₁ L₁ N₁ D₂ L₂ N₂ : ℕ}
    (hID₁ : D₁ = L₁ + 2 * N₁) (hID₂ : D₂ = L₂ + 2 * N₂) (hDeq : D₁ = D₂) :
    (∀ k, L₁ ≡ L₂ [MOD 2 ^ (k + 1)]) ↔ N₁ = N₂ := by
  constructor
  · intro hall
    refine eq_of_forall_two_pow_modEq fun k => ?_
    exact (seam_iff_rung hID₁ hID₂ (hDeq ▸ Nat.ModEq.refl _)).mp (hall k)
  · intro hNeq k
    have hLeq : L₁ = L₂ := by omega
    rw [hLeq]

/-- With a certified all-on-line finite side, the full seam tower at a window
IS the window's Riemann hypothesis (`N₁ = 0`). -/
theorem seam_tower_iff_offline_zero {D₁ L₁ N₁ D₂ L₂ N₂ : ℕ}
    (hID₁ : D₁ = L₁ + 2 * N₁) (hID₂ : D₂ = L₂ + 2 * N₂) (hDeq : D₁ = D₂)
    (hN₂ : N₂ = 0) :
    (∀ k, L₁ ≡ L₂ [MOD 2 ^ (k + 1)]) ↔ N₁ = 0 := by
  rw [seam_tower_iff_offline_eq hID₁ hID₂ hDeq, hN₂]

end RHTower

namespace RHTower

open Complex Metric

/-! ### §2 The interleaved-zeros engine (intermediate value, no argument
principle) -/

/-- `s` sign alternations of a continuous real function at `s+1` increasing
points produce `s` interleaved zeros, one strictly inside each gap. -/
theorem exists_interleaved_zeros {F : ℝ → ℝ} (hF : Continuous F) {s : ℕ}
    {ts : ℕ → ℝ} (hmono : ∀ i, i < s → ts i < ts (i + 1))
    (hsign : ∀ i, i < s → F (ts i) * F (ts (i + 1)) < 0) :
    ∃ z : ℕ → ℝ, ∀ i, i < s →
      ts i < z i ∧ z i < ts (i + 1) ∧ F (z i) = 0 := by
  classical
  have hex : ∀ i, ∃ x, i < s → (ts i < x ∧ x < ts (i + 1) ∧ F x = 0) := by
    intro i
    by_cases hi : i < s
    · have hle : ts i ≤ ts (i + 1) := (hmono i hi).le
      have hcont : ContinuousOn F (Set.Icc (ts i) (ts (i + 1))) :=
        hF.continuousOn
      rcases mul_neg_iff.mp (hsign i hi) with ⟨hpos, hneg⟩ | ⟨hneg, hpos⟩
      · have h0 : (0 : ℝ) ∈ Set.Ioo (F (ts (i + 1))) (F (ts i)) := ⟨hneg, hpos⟩
        obtain ⟨x, hx, hFx⟩ := intermediate_value_Ioo' hle hcont h0
        exact ⟨x, fun _ => ⟨hx.1, hx.2, hFx⟩⟩
      · have h0 : (0 : ℝ) ∈ Set.Ioo (F (ts i)) (F (ts (i + 1))) := ⟨hneg, hpos⟩
        obtain ⟨x, hx, hFx⟩ := intermediate_value_Ioo hle hcont h0
        exact ⟨x, fun _ => ⟨hx.1, hx.2, hFx⟩⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose z hz using hex
  exact ⟨z, fun i hi => hz i hi⟩

/-! ### §3 The critical line as a real axis for ξ -/

/-- The parametrized critical line. -/
noncomputable def linePoint (u : ℝ) : ℂ := ((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I

@[simp] theorem linePoint_re (u : ℝ) : (linePoint u).re = 1 / 2 := by
  simp [linePoint]

@[simp] theorem linePoint_im (u : ℝ) : (linePoint u).im = u := by
  simp [linePoint]

theorem linePoint_injective : Function.Injective linePoint := by
  intro u v huv
  have := congrArg Complex.im huv
  simpa using this

/-- ξ along the critical line is the complexification of a REAL function:
if its real part vanishes at `linePoint u`, ξ itself vanishes there. -/
theorem xi_linePoint_eq_zero_of_re_eq_zero {u : ℝ}
    (h : (xi (linePoint u)).re = 0) : xi (linePoint u) = 0 := by
  have him : (xi (linePoint u)).im = 0 :=
    xi_im_eq_zero_on_line (linePoint_re u)
  exact Complex.ext h him

/-! ### §4 The sign-data capstone: on-line sum = total, right-half sum = 0 -/

/-- **The seam discharge on sign-certified windows.** A peeled ξ-window whose
enclosed count is at most `s`, together with `s` certified sign alternations
of `Re ξ` along the in-window line segment, has its ENTIRE multiplicity on
the critical line: the on-line sum equals the total and the right-half sum is
zero. Turing's counting core with no argument principle: intermediate value
supplies `s` distinct on-line zeros, the peeling forces them into the
configuration, and the count squeeze leaves no room off the line. -/
theorem window_online_of_sign_data {t₁ : Finset ℂ} {m₁ : ℂ → ℕ} {h : ℂ → ℂ}
    {a : ℂ} {R : ℝ}
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    {s : ℕ} {ts : ℕ → ℝ}
    (hmono : ∀ i, i < s → ts i < ts (i + 1))
    (hsign : ∀ i, i < s →
      (xi (linePoint (ts i))).re * (xi (linePoint (ts (i + 1)))).re < 0)
    (hseg : ∀ u : ℝ, ts 0 ≤ u → u ≤ ts s → linePoint u ∈ ball a R)
    (hcount : ∑ z ∈ t₁, m₁ z ≤ s) :
    ∑ z ∈ t₁.filter (fun z => z.re = 1 / 2), m₁ z = ∑ z ∈ t₁, m₁ z ∧
      ∑ z ∈ t₁.filter (fun z => 1 / 2 < z.re), m₁ z = 0 := by
  classical
  -- the real trace of ξ along the line is continuous
  have hFcont : Continuous fun u : ℝ => (xi (linePoint u)).re := by
    have hline : Continuous linePoint := by
      unfold linePoint
      exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    exact Complex.continuous_re.comp (xi_differentiable.continuous.comp hline)
  -- the interleaved zeros
  obtain ⟨z, hz⟩ := exists_interleaved_zeros hFcont hmono hsign
  -- the monotone chain of the sign points
  have hchain : ∀ j, j ≤ s → ∀ i, i ≤ j → ts i ≤ ts j := by
    intro j
    induction j with
    | zero =>
        intro _ i hi
        rw [Nat.le_zero.mp hi]
    | succ n ih =>
        intro hns i hi
        rcases eq_or_lt_of_le hi with heq | hlt
        · rw [heq]
        · have hin : i ≤ n := Nat.lt_succ_iff.mp hlt
          have h1 : ts i ≤ ts n := ih (Nat.le_of_succ_le hns) i hin
          exact h1.trans (hmono n (Nat.lt_of_succ_le hns)).le
  -- each zero sits in the window ball
  have hzball : ∀ i, i < s → linePoint (z i) ∈ ball a R := by
    intro i hi
    have h0i : ts 0 ≤ ts i := hchain i (le_of_lt hi) 0 (Nat.zero_le i)
    have hi1s : ts (i + 1) ≤ ts s := hchain s le_rfl (i + 1) (Nat.succ_le_of_lt hi)
    exact hseg (z i) (h0i.trans (hz i hi).1.le) ((hz i hi).2.1.le.trans hi1s)
  -- each zero is a configuration point with positive multiplicity
  have hzmem : ∀ i, i < s → linePoint (z i) ∈ t₁ ∧ m₁ (linePoint (z i)) ≠ 0 := by
    intro i hi
    have hxi0 : xi (linePoint (z i)) = 0 :=
      xi_linePoint_eq_zero_of_re_eq_zero (hz i hi).2.2
    have hfz := hfact₁ _ (hzball i hi)
    rw [hxi0] at hfz
    rcases mul_eq_zero.mp hfz.symm with hp | hcontra
    · obtain ⟨w, hw, hwzero⟩ := Finset.prod_eq_zero_iff.mp hp
      rcases Nat.eq_zero_or_pos (m₁ w) with hm0 | hmpos
      · rw [hm0, pow_zero] at hwzero
        exact absurd hwzero one_ne_zero
      · have hbase : linePoint (z i) - w = 0 :=
          (pow_eq_zero_iff hmpos.ne').mp hwzero
        have hwp : w = linePoint (z i) := by
          have := sub_eq_zero.mp hbase
          exact this.symm
        rw [← hwp]
        exact ⟨hw, hmpos.ne'⟩
    · exact absurd hcontra (hh0 _ (hzball i hi))
  -- the zeros are pairwise distinct (strict interleaving)
  have hzlt : ∀ i j, i < j → j < s → z i < z j := by
    intro i j hij hjs
    have h1 : z i < ts (i + 1) := (hz i (lt_trans hij hjs)).2.1
    have h2 : ts (i + 1) ≤ ts j :=
      hchain j (le_of_lt hjs) (i + 1) (Nat.succ_le_of_lt hij)
    have h3 : ts j < z j := (hz j hjs).1
    linarith
  -- package as an image finset inside the on-line filter
  set P : Finset ℂ := (Finset.range s).image (fun i => linePoint (z i)) with hP_def
  have hPsub : P ⊆ t₁.filter (fun z => z.re = 1 / 2) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have his : i < s := Finset.mem_range.mp hi
    exact Finset.mem_filter.mpr ⟨(hzmem i his).1, linePoint_re (z i)⟩
  have hPcard : P.card = s := by
    rw [hP_def, Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    have his : i < s := Finset.mem_range.mp (Finset.mem_coe.mp hi)
    have hjs : j < s := Finset.mem_range.mp (Finset.mem_coe.mp hj)
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := hzlt i j hlt hjs
      have hzeq : z i = z j := linePoint_injective hij
      linarith
    · have := hzlt j i hgt his
      have hzeq : z i = z j := linePoint_injective hij
      linarith
  -- the squeeze: s ≤ L ≤ D ≤ s
  have hone : ∀ x ∈ P, 1 ≤ m₁ x := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have his : i < s := Finset.mem_range.mp hi
    exact Nat.one_le_iff_ne_zero.mpr (hzmem i his).2
  have hsP : s ≤ ∑ x ∈ P, m₁ x := by
    have := Finset.card_nsmul_le_sum P m₁ 1 hone
    rwa [hPcard, smul_eq_mul, mul_one] at this
  have hPL : ∑ x ∈ P, m₁ x ≤ ∑ z ∈ t₁.filter (fun z => z.re = 1 / 2), m₁ z :=
    Finset.sum_le_sum_of_subset hPsub
  have hLD : ∑ z ∈ t₁.filter (fun z => z.re = 1 / 2), m₁ z ≤ ∑ z ∈ t₁, m₁ z :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hLeq : ∑ z ∈ t₁.filter (fun z => z.re = 1 / 2), m₁ z = ∑ z ∈ t₁, m₁ z := by
    omega
  -- the identity kills the right half
  have hmr₁ : ∀ z ∈ t₁, m₁ (lineReflect z) = m₁ z := by
    intro w hw
    have h1 := xi_orderAt_lineReflect w
    have h2 := hm₁ _ (hcl₁ w hw)
    rw [h1, ← hm₁ w hw] at h2
    exact Nat.cast_inj.mp h2
  have hID := window_identity hcl₁ hmr₁
  exact ⟨hLeq, by omega⟩

/-! ### §5 The consumers: window-RH certificate, exact hL, all rungs -/

/-- **The window-RH certificate.** On a sign-certified peeled window, EVERY
zero of ξ in the ball lies on the critical line. (Off the line to the right,
its configuration multiplicity would have to be positive — but the right-half
sum is zero; to the left, reflection closure sends it to the right.) -/
theorem xi_online_of_sign_data {t₁ : Finset ℂ} {m₁ : ℂ → ℕ} {h : ℂ → ℂ}
    {a : ℂ} {R : ℝ}
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    {s : ℕ} {ts : ℕ → ℝ}
    (hmono : ∀ i, i < s → ts i < ts (i + 1))
    (hsign : ∀ i, i < s →
      (xi (linePoint (ts i))).re * (xi (linePoint (ts (i + 1)))).re < 0)
    (hseg : ∀ u : ℝ, ts 0 ≤ u → u ≤ ts s → linePoint u ∈ ball a R)
    (hcount : ∑ z ∈ t₁, m₁ z ≤ s) :
    ∀ p ∈ ball a R, xi p = 0 → p.re = 1 / 2 := by
  classical
  obtain ⟨-, hN0⟩ := window_online_of_sign_data hm₁ hcl₁ hh0 hfact₁
    hmono hsign hseg hcount
  have hright : ∀ w ∈ t₁, 1 / 2 < w.re → m₁ w = 0 := by
    intro w hw hwre
    have := Finset.sum_eq_zero_iff.mp hN0 w (Finset.mem_filter.mpr ⟨hw, hwre⟩)
    exact this
  intro p hp hxi0
  -- p is a configuration point with positive multiplicity
  have hfz := hfact₁ p hp
  rw [hxi0] at hfz
  have hpmem : p ∈ t₁ ∧ m₁ p ≠ 0 := by
    rcases mul_eq_zero.mp hfz.symm with hprod | hcontra
    · obtain ⟨w, hw, hwzero⟩ := Finset.prod_eq_zero_iff.mp hprod
      rcases Nat.eq_zero_or_pos (m₁ w) with hm0 | hmpos
      · rw [hm0, pow_zero] at hwzero
        exact absurd hwzero one_ne_zero
      · have hbase : p - w = 0 := (pow_eq_zero_iff hmpos.ne').mp hwzero
        have hwp : w = p := (sub_eq_zero.mp hbase).symm
        rw [← hwp]
        exact ⟨hw, hmpos.ne'⟩
    · exact absurd hcontra (hh0 p hp)
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- left of the line: reflect to the right
    have hqmem : lineReflect p ∈ t₁ := hcl₁ p hpmem.1
    have hqre : 1 / 2 < (lineReflect p).re := by
      have : (lineReflect p).re = 1 - p.re := by
        simp [lineReflect, Complex.sub_re, Complex.conj_re]
      rw [this]
      linarith
    have hmr : m₁ (lineReflect p) = m₁ p := by
      have h1 := xi_orderAt_lineReflect p
      have h2 := hm₁ _ hqmem
      rw [h1, ← hm₁ p hpmem.1] at h2
      exact Nat.cast_inj.mp h2
    exact hpmem.2 (hmr ▸ hright _ hqmem hqre)
  · exact hpmem.2 (hright p hpmem.1 hgt)

/-- **Exact hL from sign data and a certified on-line finite side**: both
carriers put ALL their window multiplicity on the line, and the totals agree
by domination — so the two on-line sums are EQUAL, discharging the seam
congruence hL at EVERY level `2^(k+1)` simultaneously (and with it, via
`seam_iff_rung`, every rung congruence at once). -/
theorem hL_exact_of_sign_data {N : ℕ}
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ} {h h' : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hρ₁ : ∀ w ∈ t₁, ‖w - a‖ ≤ r₀) (hρ₂ : ∀ w ∈ t₂, ‖w - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball a R)) (hh0' : ∀ z ∈ ball a R, h' z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    (hfact₂ : ∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h' z)
    (hdom : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖xi z - completedGN N z‖ < ‖completedGN N z‖)
    {s : ℕ} {ts : ℕ → ℝ}
    (hmono : ∀ i, i < s → ts i < ts (i + 1))
    (hsign : ∀ i, i < s →
      (xi (linePoint (ts i))).re * (xi (linePoint (ts (i + 1)))).re < 0)
    (hseg : ∀ u : ℝ, ts 0 ≤ u → u ≤ ts s → linePoint u ∈ ball a R)
    (hcount₂ : ∑ z ∈ t₂, m₂ z ≤ s)
    (hfin_online : ∑ z ∈ t₂.filter (fun z => z.re = 1 / 2), m₂ z
      = ∑ z ∈ t₂, m₂ z) :
    ∑ z ∈ t₁.filter (fun z => z.re = 1 / 2), m₁ z
      = ∑ z ∈ t₂.filter (fun z => z.re = 1 / 2), m₂ z := by
  have hDeq : ∑ w ∈ t₁, m₁ w = ∑ w ∈ t₂, m₂ w :=
    anneal_D_transport h0 hrR hρ₁ hρ₂ hh hh0 hh' hh0' hfact₁ hfact₂ hdom
  have hcount₁ : ∑ z ∈ t₁, m₁ z ≤ s := hDeq ▸ hcount₂
  obtain ⟨hLeq, -⟩ := window_online_of_sign_data hm₁ hcl₁ hh0 hfact₁
    hmono hsign hseg hcount₁
  rw [hLeq, hfin_online]
  exact hDeq

/-- **The dominated sign-certificate endpoint** (the instrument the certified
reader feeds): peeled carriers, domination on the charts, a finite-side count
of at most `s`, and `s` certified sign alternations force every ξ zero in the
window onto the critical line. Every hypothesis is finite certifiable data. -/
theorem xi_window_online_of_domination_sign_certificate {N : ℕ}
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ} {h h' : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hρ₁ : ∀ w ∈ t₁, ‖w - a‖ ≤ r₀) (hρ₂ : ∀ w ∈ t₂, ‖w - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball a R)) (hh0' : ∀ z ∈ ball a R, h' z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    (hfact₂ : ∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h' z)
    (hdom : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖xi z - completedGN N z‖ < ‖completedGN N z‖)
    {s : ℕ} {ts : ℕ → ℝ}
    (hmono : ∀ i, i < s → ts i < ts (i + 1))
    (hsign : ∀ i, i < s →
      (xi (linePoint (ts i))).re * (xi (linePoint (ts (i + 1)))).re < 0)
    (hseg : ∀ u : ℝ, ts 0 ≤ u → u ≤ ts s → linePoint u ∈ ball a R)
    (hcount₂ : ∑ z ∈ t₂, m₂ z ≤ s) :
    ∀ p ∈ ball a R, xi p = 0 → p.re = 1 / 2 := by
  have hDeq : ∑ w ∈ t₁, m₁ w = ∑ w ∈ t₂, m₂ w :=
    anneal_D_transport h0 hrR hρ₁ hρ₂ hh hh0 hh' hh0' hfact₁ hfact₂ hdom
  exact xi_online_of_sign_data hm₁ hcl₁ hh0 hfact₁ hmono hsign hseg
    (hDeq ▸ hcount₂)

end RHTower

namespace RHTower

open Complex Metric

/-! ### §6 The EM weld: the certificate instrument on pure finite data -/

/-- **The end-to-end finite-data window-RH certificate.** Domination is
supplied by the Euler–Maclaurin carrier (machine-checked remainder + a
finite-vs-finite closeness inequality), the count by the certified finite
side, the on-line zeros by certified sign alternations: every hypothesis is
now a finite computable inequality, and the conclusion is that every ξ zero
in the window lies on the critical line. Task #25's carrier and the seam
instrument, welded. -/
theorem xi_window_online_of_em_sign_certificate {N M : ℕ} (hM : 1 ≤ M)
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ} {h h' : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hρ₁ : ∀ w ∈ t₁, ‖w - a‖ ≤ r₀) (hρ₂ : ∀ w ∈ t₂, ‖w - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball a R)) (hh0' : ∀ z ∈ ball a R, h' z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    (hfact₂ : ∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h' z)
    (hstripC : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, 0 < z.re ∧ z ≠ 1)
    (hEM : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖z‖ * (M : ℝ) ^ (-z.re) / z.re + ‖emCarrier M z - gN N z‖ < ‖gN N z‖)
    {s : ℕ} {ts : ℕ → ℝ}
    (hmono : ∀ i, i < s → ts i < ts (i + 1))
    (hsign : ∀ i, i < s →
      (xi (linePoint (ts i))).re * (xi (linePoint (ts (i + 1)))).re < 0)
    (hseg : ∀ u : ℝ, ts 0 ≤ u → u ≤ ts s → linePoint u ∈ ball a R)
    (hcount₂ : ∑ z ∈ t₂, m₂ z ≤ s) :
    ∀ p ∈ ball a R, xi p = 0 → p.re = 1 / 2 := by
  have hdom : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖xi z - completedGN N z‖ < ‖completedGN N z‖ := by
    intro z hz
    obtain ⟨hσ, hne1⟩ := hstripC z hz
    exact completed_domination_of_em hM hσ hne1
      (Gammaℝ_ne_zero_of_re_pos hσ) (hEM z hz)
  exact xi_window_online_of_domination_sign_certificate h0 hrR hm₁ hcl₁ hρ₁
    hρ₂ hh hh0 hh' hh0' hfact₁ hfact₂ hdom hmono hsign hseg hcount₂

end RHTower

namespace RHTower

open Complex Metric

/-! ### §7 Simplicity: the tight squeeze pins every multiplicity to 1 -/

/-- **The simplicity refinement.** Under the sign-data squeeze every
configuration multiplicity is at most one: the s interleaved zeros absorb the
entire budget one unit each, other on-line points get nothing, and both
half-planes are empty (right by the squeeze, left by reflection). -/
theorem window_simple_of_sign_data {t₁ : Finset ℂ} {m₁ : ℂ → ℕ} {h : ℂ → ℂ}
    {a : ℂ} {R : ℝ}
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    {s : ℕ} {ts : ℕ → ℝ}
    (hmono : ∀ i, i < s → ts i < ts (i + 1))
    (hsign : ∀ i, i < s →
      (xi (linePoint (ts i))).re * (xi (linePoint (ts (i + 1)))).re < 0)
    (hseg : ∀ u : ℝ, ts 0 ≤ u → u ≤ ts s → linePoint u ∈ ball a R)
    (hcount : ∑ z ∈ t₁, m₁ z ≤ s) :
    ∀ w ∈ t₁, m₁ w ≤ 1 := by
  classical
  have hFcont : Continuous fun u : ℝ => (xi (linePoint u)).re := by
    have hline : Continuous linePoint := by
      unfold linePoint
      exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    exact Complex.continuous_re.comp (xi_differentiable.continuous.comp hline)
  obtain ⟨z, hz⟩ := exists_interleaved_zeros hFcont hmono hsign
  have hchain : ∀ j, j ≤ s → ∀ i, i ≤ j → ts i ≤ ts j := by
    intro j
    induction j with
    | zero =>
        intro _ i hi
        rw [Nat.le_zero.mp hi]
    | succ n ih =>
        intro hns i hi
        rcases eq_or_lt_of_le hi with heq | hlt
        · rw [heq]
        · have hin : i ≤ n := Nat.lt_succ_iff.mp hlt
          have h1 : ts i ≤ ts n := ih (Nat.le_of_succ_le hns) i hin
          exact h1.trans (hmono n (Nat.lt_of_succ_le hns)).le
  have hzball : ∀ i, i < s → linePoint (z i) ∈ ball a R := by
    intro i hi
    have h0i : ts 0 ≤ ts i := hchain i (le_of_lt hi) 0 (Nat.zero_le i)
    have hi1s : ts (i + 1) ≤ ts s := hchain s le_rfl (i + 1) (Nat.succ_le_of_lt hi)
    exact hseg (z i) (h0i.trans (hz i hi).1.le) ((hz i hi).2.1.le.trans hi1s)
  have hzmem : ∀ i, i < s → linePoint (z i) ∈ t₁ ∧ m₁ (linePoint (z i)) ≠ 0 := by
    intro i hi
    have hxi0 : xi (linePoint (z i)) = 0 :=
      xi_linePoint_eq_zero_of_re_eq_zero (hz i hi).2.2
    have hfz := hfact₁ _ (hzball i hi)
    rw [hxi0] at hfz
    rcases mul_eq_zero.mp hfz.symm with hp | hcontra
    · obtain ⟨w, hw, hwzero⟩ := Finset.prod_eq_zero_iff.mp hp
      rcases Nat.eq_zero_or_pos (m₁ w) with hm0 | hmpos
      · rw [hm0, pow_zero] at hwzero
        exact absurd hwzero one_ne_zero
      · have hbase : linePoint (z i) - w = 0 :=
          (pow_eq_zero_iff hmpos.ne').mp hwzero
        have hwp : w = linePoint (z i) := (sub_eq_zero.mp hbase).symm
        rw [← hwp]
        exact ⟨hw, hmpos.ne'⟩
    · exact absurd hcontra (hh0 _ (hzball i hi))
  have hzlt : ∀ i j, i < j → j < s → z i < z j := by
    intro i j hij hjs
    have h1 : z i < ts (i + 1) := (hz i (lt_trans hij hjs)).2.1
    have h2 : ts (i + 1) ≤ ts j :=
      hchain j (le_of_lt hjs) (i + 1) (Nat.succ_le_of_lt hij)
    have h3 : ts j < z j := (hz j hjs).1
    linarith
  set P : Finset ℂ := (Finset.range s).image (fun i => linePoint (z i)) with hP_def
  have hPsub : P ⊆ t₁.filter (fun z => z.re = 1 / 2) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have his : i < s := Finset.mem_range.mp hi
    exact Finset.mem_filter.mpr ⟨(hzmem i his).1, linePoint_re (z i)⟩
  have hPcard : P.card = s := by
    rw [hP_def, Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    have his : i < s := Finset.mem_range.mp (Finset.mem_coe.mp hi)
    have hjs : j < s := Finset.mem_range.mp (Finset.mem_coe.mp hj)
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := hzlt i j hlt hjs
      have hzeq : z i = z j := linePoint_injective hij
      linarith
    · have := hzlt j i hgt his
      have hzeq : z i = z j := linePoint_injective hij
      linarith
  have hone : ∀ x ∈ P, 1 ≤ m₁ x := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have his : i < s := Finset.mem_range.mp hi
    exact Nat.one_le_iff_ne_zero.mpr (hzmem i his).2
  have hsP : s ≤ ∑ x ∈ P, m₁ x := by
    have := Finset.card_nsmul_le_sum P m₁ 1 hone
    rwa [hPcard, smul_eq_mul, mul_one] at this
  have hPL : ∑ x ∈ P, m₁ x ≤ ∑ w ∈ t₁.filter (fun z => z.re = 1 / 2), m₁ w :=
    Finset.sum_le_sum_of_subset hPsub
  have hLD : ∑ w ∈ t₁.filter (fun z => z.re = 1 / 2), m₁ w ≤ ∑ w ∈ t₁, m₁ w :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  -- everything is tight
  have hPs : ∑ x ∈ P, m₁ x = s := by omega
  have hLs : ∑ w ∈ t₁.filter (fun z => z.re = 1 / 2), m₁ w = s := by omega
  -- inside P: exactly one each
  have hPone : ∀ x ∈ P, m₁ x = 1 := by
    intro x hx
    by_contra hne
    have h2le : 2 ≤ m₁ x := by
      have := hone x hx
      omega
    have hlt : ∑ y ∈ P, (1 : ℕ) < ∑ y ∈ P, m₁ y :=
      Finset.sum_lt_sum hone ⟨x, hx, by omega⟩
    rw [Finset.sum_const, hPcard, smul_eq_mul, mul_one, hPs] at hlt
    omega
  -- on the line but outside P: nothing
  have hout : ∀ x ∈ t₁.filter (fun z => z.re = 1 / 2) \ P, m₁ x = 0 := by
    have hsd := Finset.sum_sdiff hPsub (f := m₁)
    have hzero : ∑ x ∈ t₁.filter (fun z => z.re = 1 / 2) \ P, m₁ x = 0 := by
      omega
    exact fun x hx => Finset.sum_eq_zero_iff.mp hzero x hx
  -- right half: nothing (the squeeze)
  have hmr₁ : ∀ w ∈ t₁, m₁ (lineReflect w) = m₁ w := by
    intro w hw
    have h1 := xi_orderAt_lineReflect w
    have h2 := hm₁ _ (hcl₁ w hw)
    rw [h1, ← hm₁ w hw] at h2
    exact Nat.cast_inj.mp h2
  have hID := window_identity hcl₁ hmr₁
  have hN0 : ∑ w ∈ t₁.filter (fun z => 1 / 2 < z.re), m₁ w = 0 := by omega
  have hright : ∀ w ∈ t₁, 1 / 2 < w.re → m₁ w = 0 := by
    intro w hw hwre
    exact Finset.sum_eq_zero_iff.mp hN0 w (Finset.mem_filter.mpr ⟨hw, hwre⟩)
  -- assemble by trichotomy
  intro w hw
  rcases lt_trichotomy w.re (1 / 2) with hlt | heq | hgt
  · have hqmem : lineReflect w ∈ t₁ := hcl₁ w hw
    have hqre : 1 / 2 < (lineReflect w).re := by
      have : (lineReflect w).re = 1 - w.re := by
        simp [lineReflect, Complex.sub_re, Complex.conj_re]
      rw [this]
      linarith
    have := hright _ hqmem hqre
    rw [hmr₁ w hw] at this
    omega
  · by_cases hP : w ∈ P
    · rw [hPone w hP]
    · have hmem : w ∈ t₁.filter (fun z => z.re = 1 / 2) \ P :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hw, heq⟩, hP⟩
      rw [hout w hmem]
      omega
  · rw [hright w hw hgt]
    omega

/-- **Window RH with simplicity**: on a sign-certified peeled window, every
zero of ξ in the ball lies on the critical line AND is simple. -/
theorem xi_simple_online_of_sign_data {t₁ : Finset ℂ} {m₁ : ℂ → ℕ} {h : ℂ → ℂ}
    {a : ℂ} {R : ℝ}
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    {s : ℕ} {ts : ℕ → ℝ}
    (hmono : ∀ i, i < s → ts i < ts (i + 1))
    (hsign : ∀ i, i < s →
      (xi (linePoint (ts i))).re * (xi (linePoint (ts (i + 1)))).re < 0)
    (hseg : ∀ u : ℝ, ts 0 ≤ u → u ≤ ts s → linePoint u ∈ ball a R)
    (hcount : ∑ z ∈ t₁, m₁ z ≤ s) :
    ∀ p ∈ ball a R, xi p = 0 →
      p.re = 1 / 2 ∧ analyticOrderAt xi p = 1 := by
  have honline := xi_online_of_sign_data hm₁ hcl₁ hh0 hfact₁ hmono hsign hseg
    hcount
  have hsimple := window_simple_of_sign_data hm₁ hcl₁ hh0 hfact₁ hmono hsign
    hseg hcount
  intro p hp hxi0
  refine ⟨honline p hp hxi0, ?_⟩
  -- p is a configuration point with positive multiplicity
  have hfz := hfact₁ p hp
  rw [hxi0] at hfz
  have hpmem : p ∈ t₁ ∧ m₁ p ≠ 0 := by
    rcases mul_eq_zero.mp hfz.symm with hprod | hcontra
    · obtain ⟨w, hw, hwzero⟩ := Finset.prod_eq_zero_iff.mp hprod
      rcases Nat.eq_zero_or_pos (m₁ w) with hm0 | hmpos
      · rw [hm0, pow_zero] at hwzero
        exact absurd hwzero one_ne_zero
      · have hbase : p - w = 0 := (pow_eq_zero_iff hmpos.ne').mp hwzero
        have hwp : w = p := (sub_eq_zero.mp hbase).symm
        rw [← hwp]
        exact ⟨hw, hmpos.ne'⟩
    · exact absurd hcontra (hh0 p hp)
  have hmp : m₁ p = 1 := by
    have h1 := hsimple p hpmem.1
    have h2 := hpmem.2
    omega
  have := hm₁ p hpmem.1
  rw [hmp] at this
  exact_mod_cast this.symm

end RHTower

namespace RHTower

open Complex Metric

/-! ### §8 The simplicity squeeze, welded to domination and EM data -/

/-- **The dominated sign-certificate with simplicity.** The sign-data squeeze does
more than put all ξ zeros in the window on the critical line: after domination
transports the finite-side count, the same tight count forces every such zero to
have order one. -/
theorem xi_window_simple_online_of_domination_sign_certificate {N : ℕ}
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ} {h h' : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hρ₁ : ∀ w ∈ t₁, ‖w - a‖ ≤ r₀) (hρ₂ : ∀ w ∈ t₂, ‖w - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball a R)) (hh0' : ∀ z ∈ ball a R, h' z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    (hfact₂ : ∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h' z)
    (hdom : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖xi z - completedGN N z‖ < ‖completedGN N z‖)
    {s : ℕ} {ts : ℕ → ℝ}
    (hmono : ∀ i, i < s → ts i < ts (i + 1))
    (hsign : ∀ i, i < s →
      (xi (linePoint (ts i))).re * (xi (linePoint (ts (i + 1)))).re < 0)
    (hseg : ∀ u : ℝ, ts 0 ≤ u → u ≤ ts s → linePoint u ∈ ball a R)
    (hcount₂ : ∑ z ∈ t₂, m₂ z ≤ s) :
    ∀ p ∈ ball a R, xi p = 0 → p.re = 1 / 2 ∧ analyticOrderAt xi p = 1 := by
  have hDeq : ∑ w ∈ t₁, m₁ w = ∑ w ∈ t₂, m₂ w :=
    anneal_D_transport h0 hrR hρ₁ hρ₂ hh hh0 hh' hh0' hfact₁ hfact₂ hdom
  exact xi_simple_online_of_sign_data hm₁ hcl₁ hh0 hfact₁ hmono hsign hseg
    (hDeq ▸ hcount₂)

/-- **The EM finite-data sign-certificate with simplicity.** Euler-Maclaurin
remainder control plus finite EM-to-`gN` comparison now proves both window RH
and simplicity: any ξ zero in the certified window is on the critical line with
order exactly one. -/
theorem xi_window_simple_online_of_em_sign_certificate {N M : ℕ} (hM : 1 ≤ M)
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ} {h h' : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hρ₁ : ∀ w ∈ t₁, ‖w - a‖ ≤ r₀) (hρ₂ : ∀ w ∈ t₂, ‖w - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball a R)) (hh0' : ∀ z ∈ ball a R, h' z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    (hfact₂ : ∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h' z)
    (hstripC : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, 0 < z.re ∧ z ≠ 1)
    (hEM : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖z‖ * (M : ℝ) ^ (-z.re) / z.re + ‖emCarrier M z - gN N z‖ < ‖gN N z‖)
    {s : ℕ} {ts : ℕ → ℝ}
    (hmono : ∀ i, i < s → ts i < ts (i + 1))
    (hsign : ∀ i, i < s →
      (xi (linePoint (ts i))).re * (xi (linePoint (ts (i + 1)))).re < 0)
    (hseg : ∀ u : ℝ, ts 0 ≤ u → u ≤ ts s → linePoint u ∈ ball a R)
    (hcount₂ : ∑ z ∈ t₂, m₂ z ≤ s) :
    ∀ p ∈ ball a R, xi p = 0 → p.re = 1 / 2 ∧ analyticOrderAt xi p = 1 := by
  have hdom : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖xi z - completedGN N z‖ < ‖completedGN N z‖ := by
    intro z hz
    obtain ⟨hσ, hne1⟩ := hstripC z hz
    exact completed_domination_of_em hM hσ hne1
      (Gammaℝ_ne_zero_of_re_pos hσ) (hEM z hz)
  exact xi_window_simple_online_of_domination_sign_certificate h0 hrR hm₁ hcl₁ hρ₁
    hρ₂ hh hh0 hh' hh0' hfact₁ hfact₂ hdom hmono hsign hseg hcount₂

end RHTower
