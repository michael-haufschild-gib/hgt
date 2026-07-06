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

/-! ### §3a Generic sign squeeze for line-real carriers -/

/-- **Generic line-real sign squeeze.** A peeled carrier whose critical-line trace is
real and has `s` certified sign alternations has all its window multiplicity on the
line, provided the enclosed multiplicity budget is at most `s`. This is the common
constraint behind the ξ and completed finite-carrier readers. -/
theorem window_online_of_line_real_sign_data {F : ℂ → ℂ} {t : Finset ℂ}
    {m : ℂ → ℕ} {h : ℂ → ℂ} {a : ℂ} {R : ℝ}
    (hFcont : Continuous fun u : ℝ => (F (linePoint u)).re)
    (hline_zero : ∀ u : ℝ, (F (linePoint u)).re = 0 → F (linePoint u) = 0)
    (hclosed : ∀ z ∈ t, lineReflect z ∈ t)
    (hmrefl : ∀ z ∈ t, m (lineReflect z) = m z)
    (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hfact : ∀ z ∈ ball a R, F z = (∏ w ∈ t, (z - w) ^ m w) * h z)
    {s : ℕ} {ts : ℕ → ℝ}
    (hmono : ∀ i, i < s → ts i < ts (i + 1))
    (hsign : ∀ i, i < s →
      (F (linePoint (ts i))).re * (F (linePoint (ts (i + 1)))).re < 0)
    (hseg : ∀ u : ℝ, ts 0 ≤ u → u ≤ ts s → linePoint u ∈ ball a R)
    (hcount : ∑ z ∈ t, m z ≤ s) :
    ∑ z ∈ t.filter (fun z => z.re = 1 / 2), m z = ∑ z ∈ t, m z ∧
      ∑ z ∈ t.filter (fun z => 1 / 2 < z.re), m z = 0 := by
  classical
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
  have hzmem : ∀ i, i < s → linePoint (z i) ∈ t ∧ m (linePoint (z i)) ≠ 0 := by
    intro i hi
    have hF0 : F (linePoint (z i)) = 0 :=
      hline_zero (z i) (hz i hi).2.2
    have hfz := hfact _ (hzball i hi)
    rw [hF0] at hfz
    rcases mul_eq_zero.mp hfz.symm with hp | hcontra
    · obtain ⟨w, hw, hwzero⟩ := Finset.prod_eq_zero_iff.mp hp
      rcases Nat.eq_zero_or_pos (m w) with hm0 | hmpos
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
  have hzlt : ∀ i j, i < j → j < s → z i < z j := by
    intro i j hij hjs
    have h1 : z i < ts (i + 1) := (hz i (lt_trans hij hjs)).2.1
    have h2 : ts (i + 1) ≤ ts j :=
      hchain j (le_of_lt hjs) (i + 1) (Nat.succ_le_of_lt hij)
    have h3 : ts j < z j := (hz j hjs).1
    linarith
  set P : Finset ℂ := (Finset.range s).image (fun i => linePoint (z i)) with hP_def
  have hPsub : P ⊆ t.filter (fun z => z.re = 1 / 2) := by
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
  have hone : ∀ x ∈ P, 1 ≤ m x := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have his : i < s := Finset.mem_range.mp hi
    exact Nat.one_le_iff_ne_zero.mpr (hzmem i his).2
  have hsP : s ≤ ∑ x ∈ P, m x := by
    have := Finset.card_nsmul_le_sum P m 1 hone
    rwa [hPcard, smul_eq_mul, mul_one] at this
  have hPL : ∑ x ∈ P, m x ≤ ∑ z ∈ t.filter (fun z => z.re = 1 / 2), m z :=
    Finset.sum_le_sum_of_subset hPsub
  have hLD : ∑ z ∈ t.filter (fun z => z.re = 1 / 2), m z ≤ ∑ z ∈ t, m z :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hLeq : ∑ z ∈ t.filter (fun z => z.re = 1 / 2), m z = ∑ z ∈ t, m z := by
    omega
  have hID := window_identity hclosed hmrefl
  exact ⟨hLeq, by omega⟩

/-- Non-strict disjoint sign brackets still produce distinct zeros.  This is the bracket shape
emitted by moment/first-moment Hardy certificates: the product may be zero at an endpoint, but
disjointness of the closed brackets keeps the selected zeros distinct. -/
theorem exists_zeros_of_nonpos_brackets {F : ℝ → ℝ} (hF : Continuous F) {s : ℕ}
    {u v : ℕ → ℝ}
    (hord : ∀ i, i < s → u i ≤ v i)
    (hsign : ∀ i, i < s → F (u i) * F (v i) ≤ 0) :
    ∃ z : ℕ → ℝ, ∀ i, i < s → u i ≤ z i ∧ z i ≤ v i ∧ F (z i) = 0 := by
  classical
  have hex : ∀ i, ∃ x, i < s → u i ≤ x ∧ x ≤ v i ∧ F x = 0 := by
    intro i
    by_cases hi : i < s
    · by_cases hu0 : F (u i) = 0
      · exact ⟨u i, fun _ => ⟨le_rfl, hord i hi, hu0⟩⟩
      · by_cases hv0 : F (v i) = 0
        · exact ⟨v i, fun _ => ⟨hord i hi, le_rfl, hv0⟩⟩
        · have hprod_ne : F (u i) * F (v i) ≠ 0 := mul_ne_zero hu0 hv0
          have hprod_neg : F (u i) * F (v i) < 0 :=
            lt_of_le_of_ne (hsign i hi) hprod_ne
          have hle : u i ≤ v i := hord i hi
          have hcont : ContinuousOn F (Set.Icc (u i) (v i)) := hF.continuousOn
          rcases mul_neg_iff.mp hprod_neg with ⟨hpos, hneg⟩ | ⟨hneg, hpos⟩
          · have h0 : (0 : ℝ) ∈ Set.Ioo (F (v i)) (F (u i)) := ⟨hneg, hpos⟩
            obtain ⟨x, hx, hFx⟩ := intermediate_value_Ioo' hle hcont h0
            exact ⟨x, fun _ => ⟨hx.1.le, hx.2.le, hFx⟩⟩
          · have h0 : (0 : ℝ) ∈ Set.Ioo (F (u i)) (F (v i)) := ⟨hneg, hpos⟩
            obtain ⟨x, hx, hFx⟩ := intermediate_value_Ioo hle hcont h0
            exact ⟨x, fun _ => ⟨hx.1.le, hx.2.le, hFx⟩⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose z hz using hex
  exact ⟨z, fun i hi => hz i hi⟩

/-- Generic line-real zero squeeze from disjoint non-strict brackets.  The bracket separation
replaces strict interleaving: each bracket contributes one zero, and different brackets cannot
select the same line point. -/
theorem window_online_of_line_real_zero_brackets {F : ℂ → ℂ} {t : Finset ℂ}
    {m : ℂ → ℕ} {h : ℂ → ℂ} {a : ℂ} {R : ℝ}
    (hFcont : Continuous fun u : ℝ => (F (linePoint u)).re)
    (hline_zero : ∀ u : ℝ, (F (linePoint u)).re = 0 → F (linePoint u) = 0)
    (hclosed : ∀ z ∈ t, lineReflect z ∈ t)
    (hmrefl : ∀ z ∈ t, m (lineReflect z) = m z)
    (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hfact : ∀ z ∈ ball a R, F z = (∏ w ∈ t, (z - w) ^ m w) * h z)
    {s : ℕ} {u v : ℕ → ℝ}
    (hord : ∀ i, i < s → u i ≤ v i)
    (hsep : ∀ i j, i < j → j < s → v i < u j)
    (hsign : ∀ i, i < s →
      (F (linePoint (u i))).re * (F (linePoint (v i))).re ≤ 0)
    (hseg : ∀ i, i < s → ∀ x : ℝ, u i ≤ x → x ≤ v i → linePoint x ∈ ball a R)
    (hcount : ∑ z ∈ t, m z ≤ s) :
    ∑ z ∈ t.filter (fun z => z.re = 1 / 2), m z = ∑ z ∈ t, m z ∧
      ∑ z ∈ t.filter (fun z => 1 / 2 < z.re), m z = 0 := by
  classical
  obtain ⟨z, hz⟩ := exists_zeros_of_nonpos_brackets hFcont hord hsign
  have hzball : ∀ i, i < s → linePoint (z i) ∈ ball a R := by
    intro i hi
    exact hseg i hi (z i) (hz i hi).1 (hz i hi).2.1
  have hzmem : ∀ i, i < s → linePoint (z i) ∈ t ∧ m (linePoint (z i)) ≠ 0 := by
    intro i hi
    have hF0 : F (linePoint (z i)) = 0 :=
      hline_zero (z i) (hz i hi).2.2
    have hfz := hfact _ (hzball i hi)
    rw [hF0] at hfz
    rcases mul_eq_zero.mp hfz.symm with hp | hcontra
    · obtain ⟨w, hw, hwzero⟩ := Finset.prod_eq_zero_iff.mp hp
      rcases Nat.eq_zero_or_pos (m w) with hm0 | hmpos
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
  have hzlt : ∀ i j, i < j → j < s → z i < z j := by
    intro i j hij hjs
    have hi : i < s := lt_trans hij hjs
    have hzi : z i ≤ v i := (hz i hi).2.1
    have hzj : u j ≤ z j := (hz j hjs).1
    have hgap := hsep i j hij hjs
    linarith
  set P : Finset ℂ := (Finset.range s).image (fun i => linePoint (z i)) with hP_def
  have hPsub : P ⊆ t.filter (fun z => z.re = 1 / 2) := by
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
  have hone : ∀ x ∈ P, 1 ≤ m x := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have his : i < s := Finset.mem_range.mp hi
    exact Nat.one_le_iff_ne_zero.mpr (hzmem i his).2
  have hsP : s ≤ ∑ x ∈ P, m x := by
    have := Finset.card_nsmul_le_sum P m 1 hone
    rwa [hPcard, smul_eq_mul, mul_one] at this
  have hPL : ∑ x ∈ P, m x ≤ ∑ z ∈ t.filter (fun z => z.re = 1 / 2), m z :=
    Finset.sum_le_sum_of_subset hPsub
  have hLD : ∑ z ∈ t.filter (fun z => z.re = 1 / 2), m z ≤ ∑ z ∈ t, m z :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hLeq : ∑ z ∈ t.filter (fun z => z.re = 1 / 2), m z = ∑ z ∈ t, m z := by
    omega
  have hID := window_identity hclosed hmrefl
  exact ⟨hLeq, by omega⟩

/-- If the completed finite carrier has zero real part at a critical-line point, it
vanishes there. -/
theorem completedGN_linePoint_eq_zero_of_re_eq_zero {N : ℕ} {u : ℝ}
    (h : (completedGN N (linePoint u)).re = 0) :
    completedGN N (linePoint u) = 0 := by
  have him : (completedGN N (linePoint u)).im = 0 :=
    completedGN_im_eq_zero_on_line (linePoint_re u)
  exact Complex.ext h him

/-- **Finite-carrier sign squeeze.** Certified sign alternations of the completed
truncation on the critical-line segment force the finite-side window multiplicity
to be entirely on line. This is the finite-data discharge for the `hfin_online`
premise used by the seam congruence. -/
theorem completedGN_window_online_of_sign_data {N : ℕ}
    {t : Finset ℂ} {m : ℂ → ℕ} {h : ℂ → ℂ} {a : ℂ} {R : ℝ}
    (hstrip : ∀ z ∈ t, 0 < z.re ∧ z.re < 1)
    (hm : ∀ z ∈ t, (m z : ℕ∞) = analyticOrderAt (completedGN N) z)
    (hclosed : ∀ z ∈ t, lineReflect z ∈ t)
    (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hfact : ∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t, (z - w) ^ m w) * h z)
    {s : ℕ} {ts : ℕ → ℝ}
    (hmono : ∀ i, i < s → ts i < ts (i + 1))
    (hsign : ∀ i, i < s →
      (completedGN N (linePoint (ts i))).re *
        (completedGN N (linePoint (ts (i + 1)))).re < 0)
    (hseg : ∀ u : ℝ, ts 0 ≤ u → u ≤ ts s → linePoint u ∈ ball a R)
    (hcount : ∑ z ∈ t, m z ≤ s) :
    ∑ z ∈ t.filter (fun z => z.re = 1 / 2), m z = ∑ z ∈ t, m z ∧
      ∑ z ∈ t.filter (fun z => 1 / 2 < z.re), m z = 0 := by
  have hFcont : Continuous fun u : ℝ => (completedGN N (linePoint u)).re := by
    have hline : Continuous linePoint := by
      unfold linePoint
      exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have hcomp : Continuous fun u : ℝ => completedGN N (linePoint u) := by
      rw [continuous_iff_continuousAt]
      intro u
      exact (completedGN_analyticAt (N := N) (by rw [linePoint_re]; norm_num)
        (by rw [linePoint_re]; norm_num)).continuousAt.comp hline.continuousAt
    exact Complex.continuous_re.comp hcomp
  have hmrefl : ∀ z ∈ t, m (lineReflect z) = m z := by
    intro z hz
    obtain ⟨hz0, hz1⟩ := hstrip z hz
    have h1eq := completedGN_orderAt_lineReflect (N := N) hz0 hz1
    have h2 := hm _ (hclosed z hz)
    rw [h1eq, ← hm z hz] at h2
    exact Nat.cast_inj.mp h2
  exact window_online_of_line_real_sign_data hFcont
    (fun u h => completedGN_linePoint_eq_zero_of_re_eq_zero h)
    hclosed hmrefl hh0 hfact hmono hsign hseg hcount

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

/-- Window-RH reader from disjoint non-strict ξ brackets.  This is the closed-bracket analogue
of `xi_online_of_sign_data`, intended for Hardy moment certificates whose sign conclusion is
`≤ 0` rather than a strict alternation. -/
theorem xi_online_of_zero_brackets {t₁ : Finset ℂ} {m₁ : ℂ → ℕ} {h : ℂ → ℂ}
    {a : ℂ} {R : ℝ}
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    {s : ℕ} {u v : ℕ → ℝ}
    (hord : ∀ i, i < s → u i ≤ v i)
    (hsep : ∀ i j, i < j → j < s → v i < u j)
    (hsign : ∀ i, i < s →
      (xi (linePoint (u i))).re * (xi (linePoint (v i))).re ≤ 0)
    (hseg : ∀ i, i < s → ∀ x : ℝ, u i ≤ x → x ≤ v i → linePoint x ∈ ball a R)
    (hcount : ∑ z ∈ t₁, m₁ z ≤ s) :
    ∀ p ∈ ball a R, xi p = 0 → p.re = 1 / 2 := by
  classical
  have hFcont : Continuous fun u : ℝ => (xi (linePoint u)).re := by
    have hline : Continuous linePoint := by
      unfold linePoint
      exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    exact Complex.continuous_re.comp (xi_differentiable.continuous.comp hline)
  obtain ⟨-, hN0⟩ := window_online_of_line_real_zero_brackets hFcont
    (fun u h => xi_linePoint_eq_zero_of_re_eq_zero h)
    hcl₁ (fun z hz => by
      have h1 := xi_orderAt_lineReflect z
      have h2 := hm₁ _ (hcl₁ z hz)
      rw [h1, ← hm₁ z hz] at h2
      exact Nat.cast_inj.mp h2)
    hh0 hfact₁ hord hsep hsign hseg hcount
  have hright : ∀ w ∈ t₁, 1 / 2 < w.re → m₁ w = 0 := by
    intro w hw hwre
    exact Finset.sum_eq_zero_iff.mp hN0 w (Finset.mem_filter.mpr ⟨hw, hwre⟩)
  intro p hp hxi0
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
  · have hqmem : lineReflect p ∈ t₁ := hcl₁ p hpmem.1
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

/-- **Exact hL from two sign tables.** ξ sign alternations put ξ's window
multiplicity on the line after domination transfers the finite count bound; completed
finite-carrier sign alternations put the finite side on the line directly. Together
they discharge `hL` as equality, with no separate finite-side online premise. -/
theorem hL_exact_of_two_sign_data {N : ℕ}
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ} {h h' : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hstrip₂ : ∀ z ∈ t₂, 0 < z.re ∧ z.re < 1)
    (hm₂ : ∀ z ∈ t₂, (m₂ z : ℕ∞) = analyticOrderAt (completedGN N) z)
    (hcl₂ : ∀ z ∈ t₂, lineReflect z ∈ t₂)
    (hρ₁ : ∀ w ∈ t₁, ‖w - a‖ ≤ r₀) (hρ₂ : ∀ w ∈ t₂, ‖w - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball a R)) (hh0' : ∀ z ∈ ball a R, h' z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    (hfact₂ : ∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h' z)
    (hdom : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖xi z - completedGN N z‖ < ‖completedGN N z‖)
    {s₁ : ℕ} {ts₁ : ℕ → ℝ}
    (hmono₁ : ∀ i, i < s₁ → ts₁ i < ts₁ (i + 1))
    (hsign₁ : ∀ i, i < s₁ →
      (xi (linePoint (ts₁ i))).re * (xi (linePoint (ts₁ (i + 1)))).re < 0)
    (hseg₁ : ∀ u : ℝ, ts₁ 0 ≤ u → u ≤ ts₁ s₁ → linePoint u ∈ ball a R)
    (hcount₂₁ : ∑ z ∈ t₂, m₂ z ≤ s₁)
    {s₂ : ℕ} {ts₂ : ℕ → ℝ}
    (hmono₂ : ∀ i, i < s₂ → ts₂ i < ts₂ (i + 1))
    (hsign₂ : ∀ i, i < s₂ →
      (completedGN N (linePoint (ts₂ i))).re *
        (completedGN N (linePoint (ts₂ (i + 1)))).re < 0)
    (hseg₂ : ∀ u : ℝ, ts₂ 0 ≤ u → u ≤ ts₂ s₂ → linePoint u ∈ ball a R)
    (hcount₂₂ : ∑ z ∈ t₂, m₂ z ≤ s₂) :
    ∑ z ∈ t₁.filter (fun z => z.re = 1 / 2), m₁ z
      = ∑ z ∈ t₂.filter (fun z => z.re = 1 / 2), m₂ z := by
  obtain ⟨hfin_online, -⟩ :=
    completedGN_window_online_of_sign_data hstrip₂ hm₂ hcl₂ hh0' hfact₂
      hmono₂ hsign₂ hseg₂ hcount₂₂
  exact hL_exact_of_sign_data h0 hrR hm₁ hcl₁ hρ₁ hρ₂ hh hh0 hh' hh0'
    hfact₁ hfact₂ hdom hmono₁ hsign₁ hseg₁ hcount₂₁ hfin_online

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

/-- The EM/LOW closed-bracket endpoint: Euler-Maclaurin remainder control, finite
`emCarrier`/`gN` closeness, and a LOW floor transfer the finite count bound, while disjoint
non-strict ξ brackets supply the line zeros. -/
theorem xi_window_online_of_emCarrier_close_floor_zero_brackets
    {N M : ℕ} (hM : 1 ≤ M)
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ} {h h' : ℂ → ℂ} {a : ℂ}
    {r₀ R ε₁ δ : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hρ₁ : ∀ w ∈ t₁, ‖w - a‖ ≤ r₀) (hρ₂ : ∀ w ∈ t₂, ‖w - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball a R)) (hh0' : ∀ z ∈ ball a R, h' z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    (hfact₂ : ∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h' z)
    (hstripC : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, 0 < z.re ∧ z ≠ 1)
    (hE : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
    (hclose : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖emCarrier M z - gN N z‖ ≤ δ)
    (hF : CarrierFloorOn (chartRA a r₀ R ∪ chartLA a r₀ R) N (ε₁ + δ))
    {s : ℕ} {u v : ℕ → ℝ}
    (hord : ∀ i, i < s → u i ≤ v i)
    (hsep : ∀ i j, i < j → j < s → v i < u j)
    (hsign : ∀ i, i < s →
      (xi (linePoint (u i))).re * (xi (linePoint (v i))).re ≤ 0)
    (hseg : ∀ i, i < s → ∀ x : ℝ, u i ≤ x → x ≤ v i → linePoint x ∈ ball a R)
    (hcount₂ : ∑ z ∈ t₂, m₂ z ≤ s) :
    ∀ p ∈ ball a R, xi p = 0 → p.re = 1 / 2 := by
  have hEM : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖z‖ * (M : ℝ) ^ (-z.re) / z.re + ‖emCarrier M z - gN N z‖ < ‖gN N z‖ :=
    raw_domination_of_emCarrier_close_floor hE hclose hF
  have hdom : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖xi z - completedGN N z‖ < ‖completedGN N z‖ := by
    intro z hz
    obtain ⟨hσ, hz1⟩ := hstripC z hz
    exact completed_domination_of_em hM hσ hz1
      (Gammaℝ_ne_zero_of_re_pos hσ) (hEM z hz)
  have hDeq : ∑ w ∈ t₁, m₁ w = ∑ w ∈ t₂, m₂ w :=
    anneal_D_transport h0 hrR hρ₁ hρ₂ hh hh0 hh' hh0' hfact₁ hfact₂ hdom
  exact xi_online_of_zero_brackets hm₁ hcl₁ hh0 hfact₁ hord hsep hsign hseg
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

/-- **EM finite-side rung with hL discharged by two sign tables.** The chart
domination input is supplied by Euler-Maclaurin remainder control, and the seam
congruence input is supplied by ξ and completed finite-carrier sign squeezes. Thus a
finite-side `2^k` rung certificate transfers to ξ without any separate `hL` premise. -/
theorem xi_rung_of_finite_side_of_em_two_sign_data {N M : ℕ} (k : ℕ) (hM : 1 ≤ M)
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ} {h h' : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hstrip₂ : ∀ z ∈ t₂, 0 < z.re ∧ z.re < 1)
    (hm₂ : ∀ z ∈ t₂, (m₂ z : ℕ∞) = analyticOrderAt (completedGN N) z)
    (hcl₂ : ∀ z ∈ t₂, lineReflect z ∈ t₂)
    (hρ₁ : ∀ w ∈ t₁, ‖w - a‖ ≤ r₀) (hρ₂ : ∀ w ∈ t₂, ‖w - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball a R)) (hh0' : ∀ z ∈ ball a R, h' z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    (hfact₂ : ∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h' z)
    (hstripC : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, 0 < z.re ∧ z ≠ 1)
    (hEM : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖z‖ * (M : ℝ) ^ (-z.re) / z.re + ‖emCarrier M z - gN N z‖ < ‖gN N z‖)
    {s₁ : ℕ} {ts₁ : ℕ → ℝ}
    (hmono₁ : ∀ i, i < s₁ → ts₁ i < ts₁ (i + 1))
    (hsign₁ : ∀ i, i < s₁ →
      (xi (linePoint (ts₁ i))).re * (xi (linePoint (ts₁ (i + 1)))).re < 0)
    (hseg₁ : ∀ u : ℝ, ts₁ 0 ≤ u → u ≤ ts₁ s₁ → linePoint u ∈ ball a R)
    (hcount₂₁ : ∑ z ∈ t₂, m₂ z ≤ s₁)
    {s₂ : ℕ} {ts₂ : ℕ → ℝ}
    (hmono₂ : ∀ i, i < s₂ → ts₂ i < ts₂ (i + 1))
    (hsign₂ : ∀ i, i < s₂ →
      (completedGN N (linePoint (ts₂ i))).re *
        (completedGN N (linePoint (ts₂ (i + 1)))).re < 0)
    (hseg₂ : ∀ u : ℝ, ts₂ 0 ≤ u → u ≤ ts₂ s₂ → linePoint u ∈ ball a R)
    (hcount₂₂ : ∑ z ∈ t₂, m₂ z ≤ s₂)
    (hfin : 2 ^ k ∣ ∑ z ∈ t₂.filter (fun z => 1 / 2 < z.re), m₂ z) :
    2 ^ k ∣ ∑ z ∈ t₁.filter (fun z => 1 / 2 < z.re), m₁ z := by
  have hdom : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖xi z - completedGN N z‖ < ‖completedGN N z‖ := by
    intro z hz
    obtain ⟨hσ, hne1⟩ := hstripC z hz
    exact completed_domination_of_em hM hσ hne1
      (Gammaℝ_ne_zero_of_re_pos hσ) (hEM z hz)
  have hLeq : ∑ z ∈ t₁.filter (fun z => z.re = 1 / 2), m₁ z
      = ∑ z ∈ t₂.filter (fun z => z.re = 1 / 2), m₂ z :=
    hL_exact_of_two_sign_data h0 hrR hm₁ hcl₁ hstrip₂ hm₂ hcl₂ hρ₁ hρ₂
      hh hh0 hh' hh0' hfact₁ hfact₂ hdom hmono₁ hsign₁ hseg₁ hcount₂₁
      hmono₂ hsign₂ hseg₂ hcount₂₂
  have hL : ∑ z ∈ t₁.filter (fun z => z.re = 1 / 2), m₁ z
      ≡ ∑ z ∈ t₂.filter (fun z => z.re = 1 / 2), m₂ z [MOD 2 ^ (k + 1)] := by
    rw [hLeq]
  exact xi_rung_of_finite_side_of_domination k h0 hrR hm₁ hcl₁ hstrip₂ hm₂ hcl₂
    hρ₁ hρ₂ hh hh0 hh' hh0' hfact₁ hfact₂ hdom hL hfin

/-- **EM two-sign rung certificate with the finite-side rung discharged.** If the
completed finite carrier's own sign table fills its count budget, its right-half
count is zero, hence divisible by every `2^k`. Together with EM domination and the
ξ sign table, this proves the ξ rung with no explicit `hL` or finite-side rung
premise. -/
theorem xi_rung_of_em_two_sign_data {N M : ℕ} (k : ℕ) (hM : 1 ≤ M)
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ} {h h' : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hstrip₂ : ∀ z ∈ t₂, 0 < z.re ∧ z.re < 1)
    (hm₂ : ∀ z ∈ t₂, (m₂ z : ℕ∞) = analyticOrderAt (completedGN N) z)
    (hcl₂ : ∀ z ∈ t₂, lineReflect z ∈ t₂)
    (hρ₁ : ∀ w ∈ t₁, ‖w - a‖ ≤ r₀) (hρ₂ : ∀ w ∈ t₂, ‖w - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball a R)) (hh0' : ∀ z ∈ ball a R, h' z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    (hfact₂ : ∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h' z)
    (hstripC : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, 0 < z.re ∧ z ≠ 1)
    (hEM : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖z‖ * (M : ℝ) ^ (-z.re) / z.re + ‖emCarrier M z - gN N z‖ < ‖gN N z‖)
    {s₁ : ℕ} {ts₁ : ℕ → ℝ}
    (hmono₁ : ∀ i, i < s₁ → ts₁ i < ts₁ (i + 1))
    (hsign₁ : ∀ i, i < s₁ →
      (xi (linePoint (ts₁ i))).re * (xi (linePoint (ts₁ (i + 1)))).re < 0)
    (hseg₁ : ∀ u : ℝ, ts₁ 0 ≤ u → u ≤ ts₁ s₁ → linePoint u ∈ ball a R)
    (hcount₂₁ : ∑ z ∈ t₂, m₂ z ≤ s₁)
    {s₂ : ℕ} {ts₂ : ℕ → ℝ}
    (hmono₂ : ∀ i, i < s₂ → ts₂ i < ts₂ (i + 1))
    (hsign₂ : ∀ i, i < s₂ →
      (completedGN N (linePoint (ts₂ i))).re *
        (completedGN N (linePoint (ts₂ (i + 1)))).re < 0)
    (hseg₂ : ∀ u : ℝ, ts₂ 0 ≤ u → u ≤ ts₂ s₂ → linePoint u ∈ ball a R)
    (hcount₂₂ : ∑ z ∈ t₂, m₂ z ≤ s₂) :
    2 ^ k ∣ ∑ z ∈ t₁.filter (fun z => 1 / 2 < z.re), m₁ z := by
  obtain ⟨-, hfin_zero⟩ :=
    completedGN_window_online_of_sign_data hstrip₂ hm₂ hcl₂ hh0' hfact₂
      hmono₂ hsign₂ hseg₂ hcount₂₂
  have hfin : 2 ^ k ∣ ∑ z ∈ t₂.filter (fun z => 1 / 2 < z.re), m₂ z := by
    rw [hfin_zero]
    exact dvd_zero _
  exact xi_rung_of_finite_side_of_em_two_sign_data k hM h0 hrR hm₁ hcl₁ hstrip₂ hm₂
    hcl₂ hρ₁ hρ₂ hh hh0 hh' hh0' hfact₁ hfact₂ hstripC hEM hmono₁ hsign₁
    hseg₁ hcount₂₁ hmono₂ hsign₂ hseg₂ hcount₂₂ hfin

/-- **Shared-count EM two-sign rung certificate.** When the ξ and completed finite
carrier sign tables have the same length `s`, one finite-side count certificate
feeds both squeezes. This is the leaner form for certified readers that emit a
single count budget and two sign tables. -/
theorem xi_rung_of_em_shared_count_sign_data {N M : ℕ} (k : ℕ) (hM : 1 ≤ M)
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ} {h h' : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hstrip₂ : ∀ z ∈ t₂, 0 < z.re ∧ z.re < 1)
    (hm₂ : ∀ z ∈ t₂, (m₂ z : ℕ∞) = analyticOrderAt (completedGN N) z)
    (hcl₂ : ∀ z ∈ t₂, lineReflect z ∈ t₂)
    (hρ₁ : ∀ w ∈ t₁, ‖w - a‖ ≤ r₀) (hρ₂ : ∀ w ∈ t₂, ‖w - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball a R)) (hh0' : ∀ z ∈ ball a R, h' z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    (hfact₂ : ∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h' z)
    (hstripC : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, 0 < z.re ∧ z ≠ 1)
    (hEM : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖z‖ * (M : ℝ) ^ (-z.re) / z.re + ‖emCarrier M z - gN N z‖ < ‖gN N z‖)
    {s : ℕ} {ts₁ ts₂ : ℕ → ℝ}
    (hmono₁ : ∀ i, i < s → ts₁ i < ts₁ (i + 1))
    (hsign₁ : ∀ i, i < s →
      (xi (linePoint (ts₁ i))).re * (xi (linePoint (ts₁ (i + 1)))).re < 0)
    (hseg₁ : ∀ u : ℝ, ts₁ 0 ≤ u → u ≤ ts₁ s → linePoint u ∈ ball a R)
    (hmono₂ : ∀ i, i < s → ts₂ i < ts₂ (i + 1))
    (hsign₂ : ∀ i, i < s →
      (completedGN N (linePoint (ts₂ i))).re *
        (completedGN N (linePoint (ts₂ (i + 1)))).re < 0)
    (hseg₂ : ∀ u : ℝ, ts₂ 0 ≤ u → u ≤ ts₂ s → linePoint u ∈ ball a R)
    (hcount₂ : ∑ z ∈ t₂, m₂ z ≤ s) :
    2 ^ k ∣ ∑ z ∈ t₁.filter (fun z => 1 / 2 < z.re), m₁ z :=
  xi_rung_of_em_two_sign_data k hM h0 hrR hm₁ hcl₁ hstrip₂ hm₂ hcl₂ hρ₁ hρ₂
    hh hh0 hh' hh0' hfact₁ hfact₂ hstripC hEM hmono₁ hsign₁ hseg₁ hcount₂
    hmono₂ hsign₂ hseg₂ hcount₂

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

/-- **LOW-floor finite-data sign-certificate with simplicity.** The set-level
Euler-Maclaurin remainder bound, finite `emCarrier`/`gN` closeness, and LOW floor
replace the pointwise domination table in the one-sign EM simplicity certificate. -/
theorem xi_window_simple_online_of_emCarrier_close_floor_sign_certificate
    {N M : ℕ} (hM : 1 ≤ M)
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ} {h h' : ℂ → ℂ} {a : ℂ}
    {r₀ R ε₁ δ : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hρ₁ : ∀ w ∈ t₁, ‖w - a‖ ≤ r₀) (hρ₂ : ∀ w ∈ t₂, ‖w - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball a R)) (hh0' : ∀ z ∈ ball a R, h' z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    (hfact₂ : ∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h' z)
    (hstripC : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, 0 < z.re ∧ z ≠ 1)
    (hE : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
    (hclose : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖emCarrier M z - gN N z‖ ≤ δ)
    (hF : CarrierFloorOn (chartRA a r₀ R ∪ chartLA a r₀ R) N (ε₁ + δ))
    {s : ℕ} {ts : ℕ → ℝ}
    (hmono : ∀ i, i < s → ts i < ts (i + 1))
    (hsign : ∀ i, i < s →
      (xi (linePoint (ts i))).re * (xi (linePoint (ts (i + 1)))).re < 0)
    (hseg : ∀ u : ℝ, ts 0 ≤ u → u ≤ ts s → linePoint u ∈ ball a R)
    (hcount₂ : ∑ z ∈ t₂, m₂ z ≤ s) :
    ∀ p ∈ ball a R, xi p = 0 → p.re = 1 / 2 ∧ analyticOrderAt xi p = 1 := by
  have hEM : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖z‖ * (M : ℝ) ^ (-z.re) / z.re + ‖emCarrier M z - gN N z‖ < ‖gN N z‖ := by
    intro z hz
    exact lt_of_le_of_lt (add_le_add (hE z hz) (hclose z hz)) (hF z hz)
  exact xi_window_simple_online_of_em_sign_certificate hM h0 hrR hm₁ hcl₁ hρ₁ hρ₂
    hh hh0 hh' hh0' hfact₁ hfact₂ hstripC hEM hmono hsign hseg hcount₂

/-- **Final local-window RH gate from LOW-floor finite data.** If every hypothetical
right-half ξ-zero admits one LOW-floor EM sign certificate whose window contains it,
then RH follows. The certificate is the existing one-sign finite-data endpoint:
EM remainder bound, finite `emCarrier`/`gN` closeness, LOW floor, and a ξ sign table. -/
theorem riemannHypothesis_of_emCarrier_close_floor_sign_local_windows
    (hcert : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ N M : ℕ, ∃ t₁ t₂ : Finset ℂ, ∃ m₁ m₂ : ℂ → ℕ,
      ∃ H H' : ℂ → ℂ, ∃ a : ℂ, ∃ r₀ R ε₁ δ : ℝ, ∃ s : ℕ, ∃ ts : ℕ → ℝ,
        ρ ∈ ball a R ∧
        1 ≤ M ∧
        0 ≤ r₀ ∧ r₀ < R ∧
        (∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z) ∧
        (∀ z ∈ t₁, lineReflect z ∈ t₁) ∧
        (∀ w ∈ t₁, ‖w - a‖ ≤ r₀) ∧
        (∀ w ∈ t₂, ‖w - a‖ ≤ r₀) ∧
        AnalyticOnNhd ℂ H (ball a R) ∧
        (∀ z ∈ ball a R, H z ≠ 0) ∧
        AnalyticOnNhd ℂ H' (ball a R) ∧
        (∀ z ∈ ball a R, H' z ≠ 0) ∧
        (∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * H z) ∧
        (∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * H' z) ∧
        (∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, 0 < z.re ∧ z ≠ 1) ∧
        (∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
          ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁) ∧
        (∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
          ‖emCarrier M z - gN N z‖ ≤ δ) ∧
        CarrierFloorOn (chartRA a r₀ R ∪ chartLA a r₀ R) N (ε₁ + δ) ∧
        (∀ i, i < s → ts i < ts (i + 1)) ∧
        (∀ i, i < s →
          (xi (linePoint (ts i))).re * (xi (linePoint (ts (i + 1)))).re < 0) ∧
        (∀ u : ℝ, ts 0 ≤ u → u ≤ ts s → linePoint u ∈ ball a R) ∧
        (∑ z ∈ t₂, m₂ z ≤ s)) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro ρ hρ hzero
  rcases hcert ρ hρ hzero with
    ⟨N, M, t₁, t₂, m₁, m₂, H, H', a, r₀, R, ε₁, δ, s, ts,
      hρball, hM, h0, hrR, hm₁, hcl₁, hρ₁, hρ₂, hHan, hH0, hHpan, hHp0,
      hfact₁, hfact₂, hstripC, hE, hclose, hF, hmono, hsign, hseg, hcount₂⟩
  have hline : ρ.re = 1 / 2 :=
    (xi_window_simple_online_of_emCarrier_close_floor_sign_certificate
      (N := N) (M := M) hM h0 hrR hm₁ hcl₁ hρ₁ hρ₂ hHan hH0 hHpan hHp0
      hfact₁ hfact₂ hstripC hE hclose hF hmono hsign hseg hcount₂
      ρ hρball hzero).1
  have hright := mem_rightHalf.mp hρ
  linarith

end RHTower

namespace RHTower

open Complex Metric

/-- **Relative sign-certificate endpoint.** Relative `η < 1` closeness between ξ and
the completed finite carrier supplies the count transport used by the sign-data
window reader; certified ξ sign alternations and a finite-side count budget then
put every ξ zero in the window on the critical line, with U0 log control on the
same annulus charts. -/
theorem xi_window_online_of_relative_sign_certificate {N : ℕ}
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ} {h h' : ℂ → ℂ} {a : ℂ} {r₀ R η : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R) (hη : η < 1)
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hρ₁ : ∀ w ∈ t₁, ‖w - a‖ ≤ r₀) (hρ₂ : ∀ w ∈ t₂, ‖w - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball a R)) (hh0' : ∀ z ∈ ball a R, h' z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    (hfact₂ : ∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h' z)
    (hG0 : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, completedGN N z ≠ 0)
    (hrel : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖(xi z - completedGN N z) / completedGN N z‖ ≤ η)
    {s : ℕ} {ts : ℕ → ℝ}
    (hmono : ∀ i, i < s → ts i < ts (i + 1))
    (hsign : ∀ i, i < s →
      (xi (linePoint (ts i))).re * (xi (linePoint (ts (i + 1)))).re < 0)
    (hseg : ∀ u : ℝ, ts 0 ≤ u → u ≤ ts s → linePoint u ∈ ball a R)
    (hcount₂ : ∑ z ∈ t₂, m₂ z ≤ s) :
    (∀ p ∈ ball a R, xi p = 0 → p.re = 1 / 2) ∧
      ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
        ‖Complex.log (xi z / completedGN N z)‖ ≤
          (1 - η)⁻¹ * ‖(xi z - completedGN N z) / completedGN N z‖ := by
  obtain ⟨hDeq, hlog⟩ :=
    enclosed_count_eq_of_relative_close t₂ t₁ id m₂ id m₁ h0 hrR hη hρ₂ hρ₁
      hh' hh0' hh hh0 hfact₂ hfact₁ hG0 hrel
  exact ⟨xi_online_of_sign_data hm₁ hcl₁ hh0 hfact₁ hmono hsign hseg (hDeq ▸ hcount₂), hlog⟩

end RHTower

namespace RHTower

open Complex Metric

/-- **Relative sign-certificate with simplicity.** Relative `η < 1` closeness between
ξ and the completed finite carrier supplies the count transport used by the sign-data
squeeze; certified ξ sign alternations and a finite-side count budget then put every
ξ zero in the window on the critical line with order exactly one, while retaining the
U0 log correction bound on the annulus charts. -/
theorem xi_window_simple_online_of_relative_sign_certificate {N : ℕ}
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ} {h h' : ℂ → ℂ} {a : ℂ} {r₀ R η : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R) (hη : η < 1)
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hρ₁ : ∀ w ∈ t₁, ‖w - a‖ ≤ r₀) (hρ₂ : ∀ w ∈ t₂, ‖w - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball a R)) (hh0' : ∀ z ∈ ball a R, h' z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    (hfact₂ : ∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h' z)
    (hG0 : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, completedGN N z ≠ 0)
    (hrel : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖(xi z - completedGN N z) / completedGN N z‖ ≤ η)
    {s : ℕ} {ts : ℕ → ℝ}
    (hmono : ∀ i, i < s → ts i < ts (i + 1))
    (hsign : ∀ i, i < s →
      (xi (linePoint (ts i))).re * (xi (linePoint (ts (i + 1)))).re < 0)
    (hseg : ∀ u : ℝ, ts 0 ≤ u → u ≤ ts s → linePoint u ∈ ball a R)
    (hcount₂ : ∑ z ∈ t₂, m₂ z ≤ s) :
    (∀ p ∈ ball a R, xi p = 0 → p.re = 1 / 2 ∧ analyticOrderAt xi p = 1) ∧
      ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
        ‖Complex.log (xi z / completedGN N z)‖ ≤
          (1 - η)⁻¹ * ‖(xi z - completedGN N z) / completedGN N z‖ := by
  obtain ⟨hDeq, hlog⟩ :=
    enclosed_count_eq_of_relative_close t₂ t₁ id m₂ id m₁ h0 hrR hη hρ₂ hρ₁
      hh' hh0' hh hh0 hfact₂ hfact₁ hG0 hrel
  exact ⟨xi_simple_online_of_sign_data hm₁ hcl₁ hh0 hfact₁ hmono hsign hseg
    (hDeq ▸ hcount₂), hlog⟩

/-- **Relative sign-certificate with LOW-floor nonvanishing.**  A nonnegative
`CarrierFloorOn` certificate supplies the finite-carrier nonvanishing needed by
relative count transport, so the local sign/simplicity reader consumes the same
LOW floor interface as the finite carrier endpoints. -/
theorem xi_window_simple_online_of_relative_sign_certificate_carrierFloorOn {N : ℕ}
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ} {h h' : ℂ → ℂ} {a : ℂ}
    {r₀ R η ε : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R) (hη : η < 1) (hε : 0 ≤ ε)
    (hF : CarrierFloorOn (chartRA a r₀ R ∪ chartLA a r₀ R) N ε)
    (hchartStrip : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, 0 < z.re ∧ z ≠ 1)
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hρ₁ : ∀ w ∈ t₁, ‖w - a‖ ≤ r₀) (hρ₂ : ∀ w ∈ t₂, ‖w - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball a R)) (hh0' : ∀ z ∈ ball a R, h' z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    (hfact₂ : ∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h' z)
    (hrel : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖(xi z - completedGN N z) / completedGN N z‖ ≤ η)
    {s : ℕ} {ts : ℕ → ℝ}
    (hmono : ∀ i, i < s → ts i < ts (i + 1))
    (hsign : ∀ i, i < s →
      (xi (linePoint (ts i))).re * (xi (linePoint (ts (i + 1)))).re < 0)
    (hseg : ∀ u : ℝ, ts 0 ≤ u → u ≤ ts s → linePoint u ∈ ball a R)
    (hcount₂ : ∑ z ∈ t₂, m₂ z ≤ s) :
    (∀ p ∈ ball a R, xi p = 0 → p.re = 1 / 2 ∧ analyticOrderAt xi p = 1) ∧
      ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
        ‖Complex.log (xi z / completedGN N z)‖ ≤
          (1 - η)⁻¹ * ‖(xi z - completedGN N z) / completedGN N z‖ := by
  have hgN0 : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, gN N z ≠ 0 :=
    gN_ne_zero_of_carrierFloorOn hε hF
  have hG0 : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, completedGN N z ≠ 0 := by
    intro z hz
    obtain ⟨hσ, hz1⟩ := hchartStrip z hz
    exact completedGN_ne_zero_of_gN_ne_zero hσ hz1 (hgN0 z hz)
  exact xi_window_simple_online_of_relative_sign_certificate h0 hrR hη hm₁ hcl₁ hρ₁ hρ₂
    hh hh0 hh' hh0' hfact₁ hfact₂ hG0 hrel hmono hsign hseg hcount₂

end RHTower

namespace RHTower

open Complex Metric

/-- EM remainder control as a relative completed-carrier certificate.  The raw
Euler-Maclaurin error ratio against `gN` transfers through the common archimedean
factor to the relative ξ/completed-`gN` error used by the U0 log-bound lane. -/
theorem completed_relative_error_of_em {N M : ℕ} (hM : 1 ≤ M) {s : ℂ} {η : ℝ}
    (hσ : 0 < s.re) (hs1 : s ≠ 1) (hgN0 : gN N s ≠ 0)
    (hrel : (‖s‖ * (M : ℝ) ^ (-s.re) / s.re + ‖emCarrier M s - gN N s‖) /
      ‖gN N s‖ ≤ η) :
    ‖(xi s - completedGN N s) / completedGN N s‖ ≤ η := by
  have hs0 : s ≠ 0 := fun hs => by simp [hs] at hσ
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hσ
  have harch0 : archFactor s ≠ 0 := archFactor_ne_zero hs0 hs1 hG
  have hgnpos : 0 < ‖gN N s‖ := norm_pos_iff.mpr hgN0
  have hraw : ‖riemannZeta s - gN N s‖ ≤
      ‖s‖ * (M : ℝ) ^ (-s.re) / s.re + ‖emCarrier M s - gN N s‖ := by
    calc ‖riemannZeta s - gN N s‖
        ≤ ‖riemannZeta s - emCarrier M s‖ + ‖emCarrier M s - gN N s‖ := by
          have := dist_triangle (riemannZeta s) (emCarrier M s) (gN N s)
          simpa [dist_eq_norm] using this
      _ ≤ ‖s‖ * (M : ℝ) ^ (-s.re) / s.re + ‖emCarrier M s - gN N s‖ :=
          add_le_add (zeta_sub_emCarrier_norm_le hM hσ hs1) le_rfl
  rw [xi_sub_completedGN hs0 hs1 hG]
  unfold completedGN
  rw [norm_div, norm_mul, norm_mul]
  calc (‖archFactor s‖ * ‖riemannZeta s - gN N s‖) / (‖archFactor s‖ * ‖gN N s‖)
      = ‖riemannZeta s - gN N s‖ / ‖gN N s‖ := by
        field_simp [norm_pos_iff.mpr harch0, hgnpos.ne']
    _ ≤ (‖s‖ * (M : ℝ) ^ (-s.re) / s.re + ‖emCarrier M s - gN N s‖) /
          ‖gN N s‖ := div_le_div_of_nonneg_right hraw (norm_nonneg _)
    _ ≤ η := hrel

/-- EM relative-error transfer with raw finite-carrier nonvanishing supplied by a
nonnegative LOW floor certificate. -/
theorem completed_relative_error_of_em_of_carrierFloorOn {S : Set ℂ} {N M : ℕ}
    (hM : 1 ≤ M) {ε : ℝ} (hε : 0 ≤ ε) (hF : CarrierFloorOn S N ε)
    {s : ℂ} {η : ℝ} (hs : s ∈ S) (hσ : 0 < s.re) (hs1 : s ≠ 1)
    (hrel : (‖s‖ * (M : ℝ) ^ (-s.re) / s.re + ‖emCarrier M s - gN N s‖) /
      ‖gN N s‖ ≤ η) :
    ‖(xi s - completedGN N s) / completedGN N s‖ ≤ η :=
  completed_relative_error_of_em hM hσ hs1 (gN_ne_zero_of_carrierFloorOn hε hF s hs) hrel

/-- EM finite-data control plus a doubled LOW floor gives a uniform `1/2`
relative completed-carrier error on the same set. -/
theorem completed_relative_error_of_emCarrier_close_half_floor
    {S : Set ℂ} {N M : ℕ} (hM : 1 ≤ M) {ε₁ δ : ℝ}
    (hεδ : 0 ≤ ε₁ + δ)
    (hstrip : ∀ z ∈ S, 0 < z.re ∧ z ≠ 1)
    (hE : ∀ z ∈ S, ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
    (hclose : ∀ z ∈ S, ‖emCarrier M z - gN N z‖ ≤ δ)
    (hF : CarrierFloorOn S N (2 * (ε₁ + δ))) :
    ∀ z ∈ S, ‖(xi z - completedGN N z) / completedGN N z‖ ≤ (1 / 2 : ℝ) := by
  have hfloor_nonneg : 0 ≤ 2 * (ε₁ + δ) := mul_nonneg (by norm_num) hεδ
  intro z hz
  obtain ⟨hσ, hz1⟩ := hstrip z hz
  have hgN0 : gN N z ≠ 0 := gN_ne_zero_of_carrierFloorOn hfloor_nonneg hF z hz
  have hnum_le :
      ‖z‖ * (M : ℝ) ^ (-z.re) / z.re + ‖emCarrier M z - gN N z‖ ≤ ε₁ + δ :=
    add_le_add (hE z hz) (hclose z hz)
  have hdenpos : 0 < ‖gN N z‖ := lt_of_le_of_lt hfloor_nonneg (hF z hz)
  have hraw :
      (‖z‖ * (M : ℝ) ^ (-z.re) / z.re + ‖emCarrier M z - gN N z‖) /
        ‖gN N z‖ ≤ (1 / 2 : ℝ) := by
    have hleft :
        (‖z‖ * (M : ℝ) ^ (-z.re) / z.re + ‖emCarrier M z - gN N z‖) /
          ‖gN N z‖ ≤ (ε₁ + δ) / ‖gN N z‖ :=
      div_le_div_of_nonneg_right hnum_le (le_of_lt hdenpos)
    have hhalf : (ε₁ + δ) / ‖gN N z‖ ≤ (1 / 2 : ℝ) := by
      rw [div_le_iff₀ hdenpos]
      nlinarith [le_of_lt (hF z hz)]
    exact le_trans hleft hhalf
  exact completed_relative_error_of_em hM hσ hz1 hgN0 hraw

/-- EM finite-data deck transport with a doubled LOW floor.  The doubled floor
turns the EM numerator into a uniform `1/2` relative completed-carrier error,
so the deck transport also carries the U0 principal-log correction bound. -/
theorem anneal_deck_transport_of_emCarrier_close_half_floor {N M : ℕ}
    {F₁ F₂ G₁ G₂ : ℂ → ℂ} {a : ℂ} {R ε₁ δ : ℝ}
    (k : ℕ) (hM : 1 ≤ M) (hR : 0 < R)
    (hεδ : 0 ≤ ε₁ + δ)
    (hstrip : ∀ z ∈ chartR a R ∪ chartL a R, 0 < z.re ∧ z.re < 1)
    (hE : ∀ z ∈ chartR a R ∪ chartL a R, ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
    (hclose : ∀ z ∈ chartR a R ∪ chartL a R, ‖emCarrier M z - gN N z‖ ≤ δ)
    (hF : CarrierFloorOn (chartR a R ∪ chartL a R) N (2 * (ε₁ + δ)))
    (hF₁ : AnalyticOnNhd ℂ F₁ (chartR a R)) (hF₂ : AnalyticOnNhd ℂ F₂ (chartL a R))
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartR a R)) (hG₂ : AnalyticOnNhd ℂ G₂ (chartL a R))
    (hpF₁ : ∀ z ∈ chartR a R, F₁ z ^ 2 ^ k = xi z)
    (hpF₂ : ∀ z ∈ chartL a R, F₂ z ^ 2 ^ k = xi z)
    (hpG₁ : ∀ z ∈ chartR a R, G₁ z ^ 2 ^ k = completedGN N z)
    (hpG₂ : ∀ z ∈ chartL a R, G₂ z ^ 2 ^ k = completedGN N z) :
    deckClass F₁ F₂ (a + ((R / 2 : ℝ) : ℂ) * I) (a - ((R / 2 : ℝ) : ℂ) * I) =
        deckClass G₁ G₂ (a + ((R / 2 : ℝ) : ℂ) * I) (a - ((R / 2 : ℝ) : ℂ) * I) ∧
      ∀ z ∈ chartR a R ∪ chartL a R,
        ‖Complex.log (xi z / completedGN N z)‖ ≤
          (1 - (1 / 2 : ℝ))⁻¹ * ‖(xi z - completedGN N z) / completedGN N z‖ := by
  have hη : (1 / 2 : ℝ) < 1 := by norm_num
  have hfloor_nonneg : 0 ≤ 2 * (ε₁ + δ) := mul_nonneg (by norm_num) hεδ
  have hchartStrip : ∀ z ∈ chartR a R ∪ chartL a R, 0 < z.re ∧ z ≠ 1 := by
    intro z hz
    refine ⟨(hstrip z hz).1, ?_⟩
    intro hz1
    have hzlt : z.re < 1 := (hstrip z hz).2
    rw [hz1] at hzlt
    norm_num at hzlt
  have hrel : ∀ z ∈ chartR a R ∪ chartL a R,
      ‖(xi z - completedGN N z) / completedGN N z‖ ≤ (1 / 2 : ℝ) :=
    completed_relative_error_of_emCarrier_close_half_floor hM hεδ hchartStrip hE hclose hF
  exact anneal_deck_transport_of_relative_close_carrierFloorOn k hR hη hfloor_nonneg hF
    hchartStrip hF₁ hF₂ hG₁ hG₂ hpF₁ hpF₂ hpG₁ hpG₂ hrel

/-- EM finite-data seam L-transport with a doubled LOW floor.  The doubled floor
turns the EM numerator into a uniform `1/2` relative completed-carrier error at
both seam basepoints, so seam transport also carries both U0 principal-log
correction bounds. -/
theorem anneal_seam_L_transport_of_emCarrier_close_half_floor {N M : ℕ}
    {g₁ g₂ G₁ G₂ : ℂ → ℂ} {U : Set ℂ} {ε₁ δ : ℝ}
    (hMpos : 1 ≤ M) (hεδ : 0 ≤ ε₁ + δ)
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hUstrip : ∀ z ∈ U, 0 < z.re ∧ z.re < 1)
    (hE : ∀ z ∈ U, ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
    (hclose : ∀ z ∈ U, ‖emCarrier M z - gN N z‖ ≤ δ)
    (hF : CarrierFloorOn U N (2 * (ε₁ + δ)))
    (hg₁ : AnalyticOnNhd ℂ g₁ U) (hg₂ : AnalyticOnNhd ℂ g₂ (lineReflect ⁻¹' U))
    (hG₁ : AnalyticOnNhd ℂ G₁ U) (hG₂ : AnalyticOnNhd ℂ G₂ (lineReflect ⁻¹' U))
    (hp₁ : ∀ s ∈ U, g₁ s ^ 2 = xi s) (hp₂ : ∀ s ∈ lineReflect ⁻¹' U, g₂ s ^ 2 = xi s)
    (hP₁ : ∀ s ∈ U, G₁ s ^ 2 = completedGN N s)
    (hP₂ : ∀ s ∈ lineReflect ⁻¹' U, G₂ s ^ 2 = completedGN N s)
    {pP pM : ℂ} (hpP : pP ∈ U) (hpM : pM ∈ U)
    (hPline : pP.re = 1 / 2) (hMline : pM.re = 1 / 2) :
    deckClass g₁ g₂ pP pM = deckClass G₁ G₂ pP pM ∧
      ‖Complex.log (xi pP / completedGN N pP)‖ ≤
        (1 - (1 / 2 : ℝ))⁻¹ * ‖(xi pP - completedGN N pP) / completedGN N pP‖ ∧
      ‖Complex.log (xi pM / completedGN N pM)‖ ≤
        (1 - (1 / 2 : ℝ))⁻¹ * ‖(xi pM - completedGN N pM) / completedGN N pM‖ := by
  have hη : (1 / 2 : ℝ) < 1 := by norm_num
  have hfloor_nonneg : 0 ≤ 2 * (ε₁ + δ) := mul_nonneg (by norm_num) hεδ
  have hstrip : ∀ z ∈ U, 0 < z.re ∧ z ≠ 1 := by
    intro z hz
    refine ⟨(hUstrip z hz).1, ?_⟩
    intro hz1
    have hzlt : z.re < 1 := (hUstrip z hz).2
    rw [hz1] at hzlt
    norm_num at hzlt
  have hrel : ∀ z ∈ U, ‖(xi z - completedGN N z) / completedGN N z‖ ≤ (1 / 2 : ℝ) :=
    completed_relative_error_of_emCarrier_close_half_floor hMpos hεδ hstrip hE hclose hF
  exact anneal_seam_L_transport_of_relative_close_carrierFloorOn hη hfloor_nonneg hF
    hU hUc hUstrip hg₁ hg₂ hG₁ hG₂ hp₁ hp₂ hP₁ hP₂ hpP hpM hPline hMline
    (hrel pP hpP) (hrel pM hpM)

/-- EM-supplied relative sign-certificate with simplicity.  An explicit
Euler-Maclaurin error ratio against the finite carrier supplies the relative
ξ/completed-carrier closeness required by the U0 log-bound sign reader. -/
theorem xi_window_simple_online_of_em_relative_sign_certificate {N M : ℕ} (hM : 1 ≤ M)
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ} {h h' : ℂ → ℂ} {a : ℂ} {r₀ R η : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R) (hη : η < 1)
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hρ₁ : ∀ w ∈ t₁, ‖w - a‖ ≤ r₀) (hρ₂ : ∀ w ∈ t₂, ‖w - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball a R)) (hh0' : ∀ z ∈ ball a R, h' z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    (hfact₂ : ∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h' z)
    (hstripC : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, 0 < z.re ∧ z ≠ 1)
    (hgN0 : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, gN N z ≠ 0)
    (hEMrel : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      (‖z‖ * (M : ℝ) ^ (-z.re) / z.re + ‖emCarrier M z - gN N z‖) /
        ‖gN N z‖ ≤ η)
    {s : ℕ} {ts : ℕ → ℝ}
    (hmono : ∀ i, i < s → ts i < ts (i + 1))
    (hsign : ∀ i, i < s →
      (xi (linePoint (ts i))).re * (xi (linePoint (ts (i + 1)))).re < 0)
    (hseg : ∀ u : ℝ, ts 0 ≤ u → u ≤ ts s → linePoint u ∈ ball a R)
    (hcount₂ : ∑ z ∈ t₂, m₂ z ≤ s) :
    (∀ p ∈ ball a R, xi p = 0 → p.re = 1 / 2 ∧ analyticOrderAt xi p = 1) ∧
      ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
        ‖Complex.log (xi z / completedGN N z)‖ ≤
          (1 - η)⁻¹ * ‖(xi z - completedGN N z) / completedGN N z‖ := by
  have hG0 : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, completedGN N z ≠ 0 := by
    intro z hz
    obtain ⟨hσ, hz1⟩ := hstripC z hz
    exact completedGN_ne_zero_of_gN_ne_zero hσ hz1 (hgN0 z hz)
  have hrel : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖(xi z - completedGN N z) / completedGN N z‖ ≤ η := by
    intro z hz
    obtain ⟨hσ, hz1⟩ := hstripC z hz
    exact completed_relative_error_of_em hM hσ hz1 (hgN0 z hz) (hEMrel z hz)
  exact xi_window_simple_online_of_relative_sign_certificate h0 hrR hη hm₁ hcl₁ hρ₁ hρ₂
    hh hh0 hh' hh0' hfact₁ hfact₂ hG0 hrel hmono hsign hseg hcount₂

/-- EM-relative sign-certificate with LOW-floor nonvanishing.  A nonnegative
`CarrierFloorOn` certificate supplies the raw finite-carrier nonvanishing needed
by the EM-relative local sign/simplicity reader. -/
theorem xi_window_simple_online_of_em_relative_sign_certificate_carrierFloorOn
    {N M : ℕ} (hM : 1 ≤ M)
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ} {h h' : ℂ → ℂ} {a : ℂ}
    {r₀ R η ε : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R) (hη : η < 1) (hε : 0 ≤ ε)
    (hF : CarrierFloorOn (chartRA a r₀ R ∪ chartLA a r₀ R) N ε)
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hρ₁ : ∀ w ∈ t₁, ‖w - a‖ ≤ r₀) (hρ₂ : ∀ w ∈ t₂, ‖w - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball a R)) (hh0' : ∀ z ∈ ball a R, h' z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    (hfact₂ : ∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h' z)
    (hstripC : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, 0 < z.re ∧ z ≠ 1)
    (hEMrel : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      (‖z‖ * (M : ℝ) ^ (-z.re) / z.re + ‖emCarrier M z - gN N z‖) /
        ‖gN N z‖ ≤ η)
    {s : ℕ} {ts : ℕ → ℝ}
    (hmono : ∀ i, i < s → ts i < ts (i + 1))
    (hsign : ∀ i, i < s →
      (xi (linePoint (ts i))).re * (xi (linePoint (ts (i + 1)))).re < 0)
    (hseg : ∀ u : ℝ, ts 0 ≤ u → u ≤ ts s → linePoint u ∈ ball a R)
    (hcount₂ : ∑ z ∈ t₂, m₂ z ≤ s) :
    (∀ p ∈ ball a R, xi p = 0 → p.re = 1 / 2 ∧ analyticOrderAt xi p = 1) ∧
      ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
        ‖Complex.log (xi z / completedGN N z)‖ ≤
          (1 - η)⁻¹ * ‖(xi z - completedGN N z) / completedGN N z‖ := by
  have hgN0 : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, gN N z ≠ 0 :=
    gN_ne_zero_of_carrierFloorOn hε hF
  exact xi_window_simple_online_of_em_relative_sign_certificate hM h0 hrR hη
    hm₁ hcl₁ hρ₁ hρ₂ hh hh0 hh' hh0' hfact₁ hfact₂ hstripC hgN0 hEMrel
    hmono hsign hseg hcount₂

/-- **Final local-window RH gate from LOW-floor relative sign data.** If every
hypothetical right-half ξ-zero admits one relative sign certificate whose finite
carrier is kept nonzero by a nonnegative LOW floor, then RH follows. -/
theorem riemannHypothesis_of_relative_floor_sign_local_windows
    (hcert : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ N : ℕ, ∃ t₁ t₂ : Finset ℂ, ∃ m₁ m₂ : ℂ → ℕ,
      ∃ H H' : ℂ → ℂ, ∃ a : ℂ, ∃ r₀ R η ε : ℝ, ∃ s : ℕ, ∃ ts : ℕ → ℝ,
        ρ ∈ ball a R ∧
        0 ≤ r₀ ∧ r₀ < R ∧ η < 1 ∧ 0 ≤ ε ∧
        (∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z) ∧
        (∀ z ∈ t₁, lineReflect z ∈ t₁) ∧
        (∀ w ∈ t₁, ‖w - a‖ ≤ r₀) ∧
        (∀ w ∈ t₂, ‖w - a‖ ≤ r₀) ∧
        AnalyticOnNhd ℂ H (ball a R) ∧
        (∀ z ∈ ball a R, H z ≠ 0) ∧
        AnalyticOnNhd ℂ H' (ball a R) ∧
        (∀ z ∈ ball a R, H' z ≠ 0) ∧
        (∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * H z) ∧
        (∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * H' z) ∧
        (∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, 0 < z.re ∧ z ≠ 1) ∧
        CarrierFloorOn (chartRA a r₀ R ∪ chartLA a r₀ R) N ε ∧
        (∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
          ‖(xi z - completedGN N z) / completedGN N z‖ ≤ η) ∧
        (∀ i, i < s → ts i < ts (i + 1)) ∧
        (∀ i, i < s →
          (xi (linePoint (ts i))).re * (xi (linePoint (ts (i + 1)))).re < 0) ∧
        (∀ u : ℝ, ts 0 ≤ u → u ≤ ts s → linePoint u ∈ ball a R) ∧
        (∑ z ∈ t₂, m₂ z ≤ s)) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro ρ hρ hzero
  rcases hcert ρ hρ hzero with
    ⟨N, t₁, t₂, m₁, m₂, H, H', a, r₀, R, η, ε, s, ts,
      hρball, h0, hrR, hη, hε, hm₁, hcl₁, hρ₁, hρ₂, hHan, hH0,
      hHpan, hHp0, hfact₁, hfact₂, hchartStrip, hF, hrel, hmono, hsign,
      hseg, hcount₂⟩
  have hsimple :=
    xi_window_simple_online_of_relative_sign_certificate_carrierFloorOn
      (N := N) h0 hrR hη hε hF hchartStrip hm₁ hcl₁ hρ₁ hρ₂ hHan hH0 hHpan
      hHp0 hfact₁ hfact₂ hrel hmono hsign hseg hcount₂
  have hline : ρ.re = 1 / 2 := (hsimple.1 ρ hρball hzero).1
  have hright := mem_rightHalf.mp hρ
  linarith

/-- **Final local-window RH gate from EM-relative LOW-floor sign data.** If every
hypothetical right-half ξ-zero admits one EM-relative sign certificate whose finite
carrier is kept nonzero by a nonnegative LOW floor, then RH follows. -/
theorem riemannHypothesis_of_em_relative_floor_sign_local_windows
    (hcert : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ N M : ℕ, ∃ t₁ t₂ : Finset ℂ, ∃ m₁ m₂ : ℂ → ℕ,
      ∃ H H' : ℂ → ℂ, ∃ a : ℂ, ∃ r₀ R η ε : ℝ, ∃ s : ℕ, ∃ ts : ℕ → ℝ,
        ρ ∈ ball a R ∧
        1 ≤ M ∧
        0 ≤ r₀ ∧ r₀ < R ∧ η < 1 ∧ 0 ≤ ε ∧
        (∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z) ∧
        (∀ z ∈ t₁, lineReflect z ∈ t₁) ∧
        (∀ w ∈ t₁, ‖w - a‖ ≤ r₀) ∧
        (∀ w ∈ t₂, ‖w - a‖ ≤ r₀) ∧
        AnalyticOnNhd ℂ H (ball a R) ∧
        (∀ z ∈ ball a R, H z ≠ 0) ∧
        AnalyticOnNhd ℂ H' (ball a R) ∧
        (∀ z ∈ ball a R, H' z ≠ 0) ∧
        (∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * H z) ∧
        (∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * H' z) ∧
        (∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, 0 < z.re ∧ z ≠ 1) ∧
        CarrierFloorOn (chartRA a r₀ R ∪ chartLA a r₀ R) N ε ∧
        (∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
          (‖z‖ * (M : ℝ) ^ (-z.re) / z.re + ‖emCarrier M z - gN N z‖) /
            ‖gN N z‖ ≤ η) ∧
        (∀ i, i < s → ts i < ts (i + 1)) ∧
        (∀ i, i < s →
          (xi (linePoint (ts i))).re * (xi (linePoint (ts (i + 1)))).re < 0) ∧
        (∀ u : ℝ, ts 0 ≤ u → u ≤ ts s → linePoint u ∈ ball a R) ∧
        (∑ z ∈ t₂, m₂ z ≤ s)) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro ρ hρ hzero
  rcases hcert ρ hρ hzero with
    ⟨N, M, t₁, t₂, m₁, m₂, H, H', a, r₀, R, η, ε, s, ts,
      hρball, hM, h0, hrR, hη, hε, hm₁, hcl₁, hρ₁, hρ₂, hHan, hH0,
      hHpan, hHp0, hfact₁, hfact₂, hchartStrip, hF, hEMrel, hmono,
      hsign, hseg, hcount₂⟩
  have hsimple :=
    xi_window_simple_online_of_em_relative_sign_certificate_carrierFloorOn
      (N := N) (M := M) hM h0 hrR hη hε hF hm₁ hcl₁ hρ₁ hρ₂ hHan hH0
      hHpan hHp0 hfact₁ hfact₂ hchartStrip hEMrel hmono hsign hseg hcount₂
  have hline : ρ.re = 1 / 2 := (hsimple.1 ρ hρball hzero).1
  have hright := mem_rightHalf.mp hρ
  linarith

end RHTower

namespace RHTower

open Complex Metric

/-- EM-supplied relative finite-side rung theorem.  An explicit Euler-Maclaurin
error ratio against `gN` supplies the relative ξ/completed-carrier closeness used by
ANNEAL's U0 log-bound rung transport; finite-side divisibility then transfers to ξ
while retaining the principal-log correction control on the annulus charts. -/
theorem xi_rung_of_finite_side_of_em_relative_close {N M : ℕ} (k : ℕ) (hM : 1 ≤ M)
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ} {h h' : ℂ → ℂ} {a : ℂ} {r₀ R η : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R) (hη : η < 1)
    (hchartStrip : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, 0 < z.re ∧ z ≠ 1)
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
    (hgN0 : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, gN N z ≠ 0)
    (hEMrel : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      (‖z‖ * (M : ℝ) ^ (-z.re) / z.re + ‖emCarrier M z - gN N z‖) /
        ‖gN N z‖ ≤ η)
    (hL : ∑ z ∈ t₁.filter (fun z => z.re = 1 / 2), m₁ z
        ≡ ∑ z ∈ t₂.filter (fun z => z.re = 1 / 2), m₂ z [MOD 2 ^ (k + 1)])
    (hfin : 2 ^ k ∣ ∑ z ∈ t₂.filter (fun z => 1 / 2 < z.re), m₂ z) :
    (2 ^ k ∣ ∑ z ∈ t₁.filter (fun z => 1 / 2 < z.re), m₁ z) ∧
      ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
        ‖Complex.log (xi z / completedGN N z)‖ ≤
          (1 - η)⁻¹ * ‖(xi z - completedGN N z) / completedGN N z‖ := by
  have hG0 : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, completedGN N z ≠ 0 := by
    intro z hz
    obtain ⟨hσ, hz1⟩ := hchartStrip z hz
    exact completedGN_ne_zero_of_gN_ne_zero hσ hz1 (hgN0 z hz)
  have hrel : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖(xi z - completedGN N z) / completedGN N z‖ ≤ η := by
    intro z hz
    obtain ⟨hσ, hz1⟩ := hchartStrip z hz
    exact completed_relative_error_of_em hM hσ hz1 (hgN0 z hz) (hEMrel z hz)
  exact xi_rung_of_finite_side_of_relative_close k h0 hrR hη hm₁ hcl₁ hstrip hm₂ hcl₂ hρ₁
    hρ₂ hh hh0 hh' hh0' hfact₁ hfact₂ hG0 hrel hL hfin

end RHTower

namespace RHTower

open Complex Metric

/-- **Relative EM two-sign parity certificate.** The explicit Euler-Maclaurin
relative error ratio supplies relative ξ/completed-carrier control; the two sign
tables discharge the seam `hL` congruence, giving the ANNEAL right-half window-count
congruence and the U0 principal-log correction bound. -/
theorem xi_window_parity_of_em_relative_two_sign_data {N M : ℕ} (k : ℕ) (hM : 1 ≤ M)
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ} {h h' : ℂ → ℂ} {a : ℂ} {r₀ R η : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R) (hη : η < 1)
    (hchartStrip : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, 0 < z.re ∧ z ≠ 1)
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hstrip₂ : ∀ z ∈ t₂, 0 < z.re ∧ z.re < 1)
    (hm₂ : ∀ z ∈ t₂, (m₂ z : ℕ∞) = analyticOrderAt (completedGN N) z)
    (hcl₂ : ∀ z ∈ t₂, lineReflect z ∈ t₂)
    (hρ₁ : ∀ w ∈ t₁, ‖w - a‖ ≤ r₀) (hρ₂ : ∀ w ∈ t₂, ‖w - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball a R)) (hh0' : ∀ z ∈ ball a R, h' z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    (hfact₂ : ∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h' z)
    (hgN0 : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, gN N z ≠ 0)
    (hEMrel : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      (‖z‖ * (M : ℝ) ^ (-z.re) / z.re + ‖emCarrier M z - gN N z‖) /
        ‖gN N z‖ ≤ η)
    {s₁ : ℕ} {ts₁ : ℕ → ℝ}
    (hmono₁ : ∀ i, i < s₁ → ts₁ i < ts₁ (i + 1))
    (hsign₁ : ∀ i, i < s₁ →
      (xi (linePoint (ts₁ i))).re * (xi (linePoint (ts₁ (i + 1)))).re < 0)
    (hseg₁ : ∀ u : ℝ, ts₁ 0 ≤ u → u ≤ ts₁ s₁ → linePoint u ∈ ball a R)
    (hcount₂₁ : ∑ z ∈ t₂, m₂ z ≤ s₁)
    {s₂ : ℕ} {ts₂ : ℕ → ℝ}
    (hmono₂ : ∀ i, i < s₂ → ts₂ i < ts₂ (i + 1))
    (hsign₂ : ∀ i, i < s₂ →
      (completedGN N (linePoint (ts₂ i))).re *
        (completedGN N (linePoint (ts₂ (i + 1)))).re < 0)
    (hseg₂ : ∀ u : ℝ, ts₂ 0 ≤ u → u ≤ ts₂ s₂ → linePoint u ∈ ball a R)
    (hcount₂₂ : ∑ z ∈ t₂, m₂ z ≤ s₂) :
    (∑ z ∈ t₁.filter (fun z => 1 / 2 < z.re), m₁ z
      ≡ ∑ z ∈ t₂.filter (fun z => 1 / 2 < z.re), m₂ z [MOD 2 ^ k]) ∧
      ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
        ‖Complex.log (xi z / completedGN N z)‖ ≤
          (1 - η)⁻¹ * ‖(xi z - completedGN N z) / completedGN N z‖ := by
  have hG0 : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, completedGN N z ≠ 0 := by
    intro z hz
    obtain ⟨hσ, hz1⟩ := hchartStrip z hz
    exact completedGN_ne_zero_of_gN_ne_zero hσ hz1 (hgN0 z hz)
  have hrel : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖(xi z - completedGN N z) / completedGN N z‖ ≤ η := by
    intro z hz
    obtain ⟨hσ, hz1⟩ := hchartStrip z hz
    exact completed_relative_error_of_em hM hσ hz1 (hgN0 z hz) (hEMrel z hz)
  have hdom : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖xi z - completedGN N z‖ < ‖completedGN N z‖ := by
    intro z hz
    have hzrel := hrel z hz
    rw [norm_div] at hzrel
    have hpos : 0 < ‖completedGN N z‖ := norm_pos_iff.mpr (hG0 z hz)
    have hmul := mul_le_mul_of_nonneg_right hzrel (le_of_lt hpos)
    rw [div_mul_cancel₀ _ hpos.ne'] at hmul
    exact lt_of_le_of_lt hmul (by simpa using mul_lt_mul_of_pos_right hη hpos)
  have hLeq : ∑ z ∈ t₁.filter (fun z => z.re = 1 / 2), m₁ z
      = ∑ z ∈ t₂.filter (fun z => z.re = 1 / 2), m₂ z :=
    hL_exact_of_two_sign_data h0 hrR hm₁ hcl₁ hstrip₂ hm₂ hcl₂ hρ₁ hρ₂
      hh hh0 hh' hh0' hfact₁ hfact₂ hdom hmono₁ hsign₁ hseg₁ hcount₂₁
      hmono₂ hsign₂ hseg₂ hcount₂₂
  have hL : ∑ z ∈ t₁.filter (fun z => z.re = 1 / 2), m₁ z
      ≡ ∑ z ∈ t₂.filter (fun z => z.re = 1 / 2), m₂ z [MOD 2 ^ (k + 1)] := by
    rw [hLeq]
  exact anneal_window_parity_transport_of_relative_close_gN_nonzero k h0 hrR hη
    hchartStrip hm₁ hcl₁ hstrip₂ hm₂ hcl₂ hρ₁ hρ₂ hh hh0 hh' hh0' hfact₁ hfact₂
    hgN0 hrel hL

/-- **Relative EM two-sign rung certificate with the finite-side rung discharged.**
The completed finite carrier's sign table proves its right-half count is zero, while
relative EM control supplies the ANNEAL count transport and U0 log bound. Thus the ξ
rung and the principal-log correction estimate come from two sign tables plus the
relative Euler-Maclaurin certificate, with no separate finite-side rung premise. -/
theorem xi_rung_of_em_relative_two_sign_data {N M : ℕ} (k : ℕ) (hM : 1 ≤ M)
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ} {h h' : ℂ → ℂ} {a : ℂ} {r₀ R η : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R) (hη : η < 1)
    (hchartStrip : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, 0 < z.re ∧ z ≠ 1)
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hstrip₂ : ∀ z ∈ t₂, 0 < z.re ∧ z.re < 1)
    (hm₂ : ∀ z ∈ t₂, (m₂ z : ℕ∞) = analyticOrderAt (completedGN N) z)
    (hcl₂ : ∀ z ∈ t₂, lineReflect z ∈ t₂)
    (hρ₁ : ∀ w ∈ t₁, ‖w - a‖ ≤ r₀) (hρ₂ : ∀ w ∈ t₂, ‖w - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball a R)) (hh0' : ∀ z ∈ ball a R, h' z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    (hfact₂ : ∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h' z)
    (hgN0 : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, gN N z ≠ 0)
    (hEMrel : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      (‖z‖ * (M : ℝ) ^ (-z.re) / z.re + ‖emCarrier M z - gN N z‖) /
        ‖gN N z‖ ≤ η)
    {s₁ : ℕ} {ts₁ : ℕ → ℝ}
    (hmono₁ : ∀ i, i < s₁ → ts₁ i < ts₁ (i + 1))
    (hsign₁ : ∀ i, i < s₁ →
      (xi (linePoint (ts₁ i))).re * (xi (linePoint (ts₁ (i + 1)))).re < 0)
    (hseg₁ : ∀ u : ℝ, ts₁ 0 ≤ u → u ≤ ts₁ s₁ → linePoint u ∈ ball a R)
    (hcount₂₁ : ∑ z ∈ t₂, m₂ z ≤ s₁)
    {s₂ : ℕ} {ts₂ : ℕ → ℝ}
    (hmono₂ : ∀ i, i < s₂ → ts₂ i < ts₂ (i + 1))
    (hsign₂ : ∀ i, i < s₂ →
      (completedGN N (linePoint (ts₂ i))).re *
        (completedGN N (linePoint (ts₂ (i + 1)))).re < 0)
    (hseg₂ : ∀ u : ℝ, ts₂ 0 ≤ u → u ≤ ts₂ s₂ → linePoint u ∈ ball a R)
    (hcount₂₂ : ∑ z ∈ t₂, m₂ z ≤ s₂) :
    (2 ^ k ∣ ∑ z ∈ t₁.filter (fun z => 1 / 2 < z.re), m₁ z) ∧
      ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
        ‖Complex.log (xi z / completedGN N z)‖ ≤
          (1 - η)⁻¹ * ‖(xi z - completedGN N z) / completedGN N z‖ := by
  obtain ⟨hparity, hlog⟩ :=
    xi_window_parity_of_em_relative_two_sign_data k hM h0 hrR hη hchartStrip hm₁ hcl₁
      hstrip₂ hm₂ hcl₂ hρ₁ hρ₂ hh hh0 hh' hh0' hfact₁ hfact₂ hgN0 hEMrel
      hmono₁ hsign₁ hseg₁ hcount₂₁ hmono₂ hsign₂ hseg₂ hcount₂₂
  obtain ⟨-, hfin_zero⟩ :=
    completedGN_window_online_of_sign_data hstrip₂ hm₂ hcl₂ hh0' hfact₂
      hmono₂ hsign₂ hseg₂ hcount₂₂
  have hfin : 2 ^ k ∣ ∑ z ∈ t₂.filter (fun z => 1 / 2 < z.re), m₂ z := by
    rw [hfin_zero]
    exact dvd_zero _
  have hrung : 2 ^ k ∣ ∑ z ∈ t₁.filter (fun z => 1 / 2 < z.re), m₁ z :=
    Nat.modEq_zero_iff_dvd.mp (hparity.trans (Nat.modEq_zero_iff_dvd.mpr hfin))
  exact ⟨hrung, hlog⟩

end RHTower

namespace RHTower

open Complex Metric

/-- **Relative EM two-sign joint certificate.**  The same finite EM-relative data
certifies the ξ window zeros as on-line simple zeros and transfers the finite-side
rung to ξ, while retaining the U0 principal-log correction bound. -/
theorem xi_simple_window_and_rung_of_em_relative_two_sign_data {N M : ℕ} (k : ℕ) (hM : 1 ≤ M)
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ} {h h' : ℂ → ℂ} {a : ℂ} {r₀ R η : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R) (hη : η < 1)
    (hchartStrip : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, 0 < z.re ∧ z ≠ 1)
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hstrip₂ : ∀ z ∈ t₂, 0 < z.re ∧ z.re < 1)
    (hm₂ : ∀ z ∈ t₂, (m₂ z : ℕ∞) = analyticOrderAt (completedGN N) z)
    (hcl₂ : ∀ z ∈ t₂, lineReflect z ∈ t₂)
    (hρ₁ : ∀ w ∈ t₁, ‖w - a‖ ≤ r₀) (hρ₂ : ∀ w ∈ t₂, ‖w - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball a R)) (hh0' : ∀ z ∈ ball a R, h' z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    (hfact₂ : ∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h' z)
    (hgN0 : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, gN N z ≠ 0)
    (hEMrel : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      (‖z‖ * (M : ℝ) ^ (-z.re) / z.re + ‖emCarrier M z - gN N z‖) /
        ‖gN N z‖ ≤ η)
    {s₁ : ℕ} {ts₁ : ℕ → ℝ}
    (hmono₁ : ∀ i, i < s₁ → ts₁ i < ts₁ (i + 1))
    (hsign₁ : ∀ i, i < s₁ →
      (xi (linePoint (ts₁ i))).re * (xi (linePoint (ts₁ (i + 1)))).re < 0)
    (hseg₁ : ∀ u : ℝ, ts₁ 0 ≤ u → u ≤ ts₁ s₁ → linePoint u ∈ ball a R)
    (hcount₂₁ : ∑ z ∈ t₂, m₂ z ≤ s₁)
    {s₂ : ℕ} {ts₂ : ℕ → ℝ}
    (hmono₂ : ∀ i, i < s₂ → ts₂ i < ts₂ (i + 1))
    (hsign₂ : ∀ i, i < s₂ →
      (completedGN N (linePoint (ts₂ i))).re *
        (completedGN N (linePoint (ts₂ (i + 1)))).re < 0)
    (hseg₂ : ∀ u : ℝ, ts₂ 0 ≤ u → u ≤ ts₂ s₂ → linePoint u ∈ ball a R)
    (hcount₂₂ : ∑ z ∈ t₂, m₂ z ≤ s₂) :
    (∀ p ∈ ball a R, xi p = 0 → p.re = 1 / 2 ∧ analyticOrderAt xi p = 1) ∧
      (2 ^ k ∣ ∑ z ∈ t₁.filter (fun z => 1 / 2 < z.re), m₁ z) ∧
        ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
          ‖Complex.log (xi z / completedGN N z)‖ ≤
            (1 - η)⁻¹ * ‖(xi z - completedGN N z) / completedGN N z‖ := by
  have hsimple :=
    xi_window_simple_online_of_em_relative_sign_certificate hM h0 hrR hη hm₁ hcl₁ hρ₁ hρ₂
      hh hh0 hh' hh0' hfact₁ hfact₂ hchartStrip hgN0 hEMrel hmono₁ hsign₁ hseg₁ hcount₂₁
  have hrung :=
    xi_rung_of_em_relative_two_sign_data k hM h0 hrR hη hchartStrip hm₁ hcl₁ hstrip₂ hm₂ hcl₂
      hρ₁ hρ₂ hh hh0 hh' hh0' hfact₁ hfact₂ hgN0 hEMrel hmono₁ hsign₁ hseg₁ hcount₂₁
      hmono₂ hsign₂ hseg₂ hcount₂₂
  exact ⟨hsimple.1, hrung.1, hrung.2⟩

/-- **EM-relative LOW-floor two-sign joint certificate.** A nonnegative LOW floor
discharges the raw finite-carrier nonvanishing side condition in the strongest
EM-relative two-sign endpoint, while preserving ξ simplicity, dyadic rung
divisibility, and U0 principal-log control. -/
theorem xi_simple_window_and_rung_of_em_relative_two_sign_data_carrierFloorOn
    {N M : ℕ} (k : ℕ) (hM : 1 ≤ M)
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ} {h h' : ℂ → ℂ} {a : ℂ}
    {r₀ R η ε : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R) (hη : η < 1) (hε : 0 ≤ ε)
    (hF : CarrierFloorOn (chartRA a r₀ R ∪ chartLA a r₀ R) N ε)
    (hchartStrip : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, 0 < z.re ∧ z ≠ 1)
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hstrip₂ : ∀ z ∈ t₂, 0 < z.re ∧ z.re < 1)
    (hm₂ : ∀ z ∈ t₂, (m₂ z : ℕ∞) = analyticOrderAt (completedGN N) z)
    (hcl₂ : ∀ z ∈ t₂, lineReflect z ∈ t₂)
    (hρ₁ : ∀ w ∈ t₁, ‖w - a‖ ≤ r₀) (hρ₂ : ∀ w ∈ t₂, ‖w - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball a R)) (hh0' : ∀ z ∈ ball a R, h' z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    (hfact₂ : ∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h' z)
    (hEMrel : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      (‖z‖ * (M : ℝ) ^ (-z.re) / z.re + ‖emCarrier M z - gN N z‖) /
        ‖gN N z‖ ≤ η)
    {s₁ : ℕ} {ts₁ : ℕ → ℝ}
    (hmono₁ : ∀ i, i < s₁ → ts₁ i < ts₁ (i + 1))
    (hsign₁ : ∀ i, i < s₁ →
      (xi (linePoint (ts₁ i))).re * (xi (linePoint (ts₁ (i + 1)))).re < 0)
    (hseg₁ : ∀ u : ℝ, ts₁ 0 ≤ u → u ≤ ts₁ s₁ → linePoint u ∈ ball a R)
    (hcount₂₁ : ∑ z ∈ t₂, m₂ z ≤ s₁)
    {s₂ : ℕ} {ts₂ : ℕ → ℝ}
    (hmono₂ : ∀ i, i < s₂ → ts₂ i < ts₂ (i + 1))
    (hsign₂ : ∀ i, i < s₂ →
      (completedGN N (linePoint (ts₂ i))).re *
        (completedGN N (linePoint (ts₂ (i + 1)))).re < 0)
    (hseg₂ : ∀ u : ℝ, ts₂ 0 ≤ u → u ≤ ts₂ s₂ → linePoint u ∈ ball a R)
    (hcount₂₂ : ∑ z ∈ t₂, m₂ z ≤ s₂) :
    (∀ p ∈ ball a R, xi p = 0 → p.re = 1 / 2 ∧ analyticOrderAt xi p = 1) ∧
      (2 ^ k ∣ ∑ z ∈ t₁.filter (fun z => 1 / 2 < z.re), m₁ z) ∧
        ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
          ‖Complex.log (xi z / completedGN N z)‖ ≤
            (1 - η)⁻¹ * ‖(xi z - completedGN N z) / completedGN N z‖ := by
  have hgN0 : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, gN N z ≠ 0 :=
    gN_ne_zero_of_carrierFloorOn hε hF
  exact xi_simple_window_and_rung_of_em_relative_two_sign_data k hM h0 hrR hη
    hchartStrip hm₁ hcl₁ hstrip₂ hm₂ hcl₂ hρ₁ hρ₂ hh hh0 hh' hh0'
    hfact₁ hfact₂ hgN0 hEMrel hmono₁ hsign₁ hseg₁ hcount₂₁
    hmono₂ hsign₂ hseg₂ hcount₂₂

end RHTower

namespace RHTower

open Complex Metric

/-- **Relative sign-certificate with raw finite-carrier nonvanishing.**  The
completed-carrier nonvanishing needed by the relative count transport is derived
from strip data and `gN` nonvanishing, so the sign/simplicity certificate can consume
the finite carrier's natural nonzero check directly. -/
theorem xi_window_simple_online_of_relative_sign_certificate_gN_nonzero {N : ℕ}
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ} {h h' : ℂ → ℂ} {a : ℂ} {r₀ R η : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R) (hη : η < 1)
    (hchartStrip : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, 0 < z.re ∧ z ≠ 1)
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hρ₁ : ∀ w ∈ t₁, ‖w - a‖ ≤ r₀) (hρ₂ : ∀ w ∈ t₂, ‖w - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball a R)) (hh0' : ∀ z ∈ ball a R, h' z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    (hfact₂ : ∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h' z)
    (hgN0 : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, gN N z ≠ 0)
    (hrel : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖(xi z - completedGN N z) / completedGN N z‖ ≤ η)
    {s : ℕ} {ts : ℕ → ℝ}
    (hmono : ∀ i, i < s → ts i < ts (i + 1))
    (hsign : ∀ i, i < s →
      (xi (linePoint (ts i))).re * (xi (linePoint (ts (i + 1)))).re < 0)
    (hseg : ∀ u : ℝ, ts 0 ≤ u → u ≤ ts s → linePoint u ∈ ball a R)
    (hcount₂ : ∑ z ∈ t₂, m₂ z ≤ s) :
    (∀ p ∈ ball a R, xi p = 0 → p.re = 1 / 2 ∧ analyticOrderAt xi p = 1) ∧
      ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
        ‖Complex.log (xi z / completedGN N z)‖ ≤
          (1 - η)⁻¹ * ‖(xi z - completedGN N z) / completedGN N z‖ := by
  have hG0 : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, completedGN N z ≠ 0 := by
    intro z hz
    obtain ⟨hσ, hz1⟩ := hchartStrip z hz
    exact completedGN_ne_zero_of_gN_ne_zero hσ hz1 (hgN0 z hz)
  exact xi_window_simple_online_of_relative_sign_certificate h0 hrR hη hm₁ hcl₁ hρ₁ hρ₂
    hh hh0 hh' hh0' hfact₁ hfact₂ hG0 hrel hmono hsign hseg hcount₂

end RHTower

namespace RHTower

open Complex Metric

/-- **Strict EM two-sign joint certificate.** The same finite EM domination data
certifies the ξ window zeros as on-line simple zeros and transfers the completed
finite-side rung to ξ. -/
theorem xi_simple_window_and_rung_of_em_two_sign_data {N M : ℕ} (k : ℕ) (hM : 1 ≤ M)
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ} {h h' : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hstrip₂ : ∀ z ∈ t₂, 0 < z.re ∧ z.re < 1)
    (hm₂ : ∀ z ∈ t₂, (m₂ z : ℕ∞) = analyticOrderAt (completedGN N) z)
    (hcl₂ : ∀ z ∈ t₂, lineReflect z ∈ t₂)
    (hρ₁ : ∀ w ∈ t₁, ‖w - a‖ ≤ r₀) (hρ₂ : ∀ w ∈ t₂, ‖w - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball a R)) (hh0' : ∀ z ∈ ball a R, h' z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    (hfact₂ : ∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h' z)
    (hstripC : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, 0 < z.re ∧ z ≠ 1)
    (hEM : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖z‖ * (M : ℝ) ^ (-z.re) / z.re + ‖emCarrier M z - gN N z‖ < ‖gN N z‖)
    {s₁ : ℕ} {ts₁ : ℕ → ℝ}
    (hmono₁ : ∀ i, i < s₁ → ts₁ i < ts₁ (i + 1))
    (hsign₁ : ∀ i, i < s₁ →
      (xi (linePoint (ts₁ i))).re * (xi (linePoint (ts₁ (i + 1)))).re < 0)
    (hseg₁ : ∀ u : ℝ, ts₁ 0 ≤ u → u ≤ ts₁ s₁ → linePoint u ∈ ball a R)
    (hcount₂₁ : ∑ z ∈ t₂, m₂ z ≤ s₁)
    {s₂ : ℕ} {ts₂ : ℕ → ℝ}
    (hmono₂ : ∀ i, i < s₂ → ts₂ i < ts₂ (i + 1))
    (hsign₂ : ∀ i, i < s₂ →
      (completedGN N (linePoint (ts₂ i))).re *
        (completedGN N (linePoint (ts₂ (i + 1)))).re < 0)
    (hseg₂ : ∀ u : ℝ, ts₂ 0 ≤ u → u ≤ ts₂ s₂ → linePoint u ∈ ball a R)
    (hcount₂₂ : ∑ z ∈ t₂, m₂ z ≤ s₂) :
    (∀ p ∈ ball a R, xi p = 0 → p.re = 1 / 2 ∧ analyticOrderAt xi p = 1) ∧
      2 ^ k ∣ ∑ z ∈ t₁.filter (fun z => 1 / 2 < z.re), m₁ z := by
  have hsimple :=
    xi_window_simple_online_of_em_sign_certificate hM h0 hrR hm₁ hcl₁ hρ₁ hρ₂
      hh hh0 hh' hh0' hfact₁ hfact₂ hstripC hEM hmono₁ hsign₁ hseg₁ hcount₂₁
  have hrung :=
    xi_rung_of_em_two_sign_data k hM h0 hrR hm₁ hcl₁ hstrip₂ hm₂ hcl₂
      hρ₁ hρ₂ hh hh0 hh' hh0' hfact₁ hfact₂ hstripC hEM hmono₁ hsign₁ hseg₁ hcount₂₁
      hmono₂ hsign₂ hseg₂ hcount₂₂
  exact ⟨hsimple, hrung⟩

/-- Strict finite-data LOW-floor two-sign joint certificate.  The set-level
Euler-Maclaurin remainder bound, finite `emCarrier`/`gN` closeness, and LOW floor
replace the pointwise domination table in the strict EM joint certificate. -/
theorem xi_simple_window_and_rung_of_emCarrier_close_floor_two_sign_data
    {N M : ℕ} (k : ℕ) (hM : 1 ≤ M)
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ} {h h' : ℂ → ℂ} {a : ℂ}
    {r₀ R ε₁ δ : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hchartStrip : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, 0 < z.re ∧ z ≠ 1)
    (hE : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
    (hclose : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖emCarrier M z - gN N z‖ ≤ δ)
    (hF : CarrierFloorOn (chartRA a r₀ R ∪ chartLA a r₀ R) N (ε₁ + δ))
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hstrip₂ : ∀ z ∈ t₂, 0 < z.re ∧ z.re < 1)
    (hm₂ : ∀ z ∈ t₂, (m₂ z : ℕ∞) = analyticOrderAt (completedGN N) z)
    (hcl₂ : ∀ z ∈ t₂, lineReflect z ∈ t₂)
    (hρ₁ : ∀ w ∈ t₁, ‖w - a‖ ≤ r₀) (hρ₂ : ∀ w ∈ t₂, ‖w - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball a R)) (hh0' : ∀ z ∈ ball a R, h' z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    (hfact₂ : ∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h' z)
    {s₁ : ℕ} {ts₁ : ℕ → ℝ}
    (hmono₁ : ∀ i, i < s₁ → ts₁ i < ts₁ (i + 1))
    (hsign₁ : ∀ i, i < s₁ →
      (xi (linePoint (ts₁ i))).re * (xi (linePoint (ts₁ (i + 1)))).re < 0)
    (hseg₁ : ∀ u : ℝ, ts₁ 0 ≤ u → u ≤ ts₁ s₁ → linePoint u ∈ ball a R)
    (hcount₂₁ : ∑ z ∈ t₂, m₂ z ≤ s₁)
    {s₂ : ℕ} {ts₂ : ℕ → ℝ}
    (hmono₂ : ∀ i, i < s₂ → ts₂ i < ts₂ (i + 1))
    (hsign₂ : ∀ i, i < s₂ →
      (completedGN N (linePoint (ts₂ i))).re *
        (completedGN N (linePoint (ts₂ (i + 1)))).re < 0)
    (hseg₂ : ∀ u : ℝ, ts₂ 0 ≤ u → u ≤ ts₂ s₂ → linePoint u ∈ ball a R)
    (hcount₂₂ : ∑ z ∈ t₂, m₂ z ≤ s₂) :
    (∀ p ∈ ball a R, xi p = 0 → p.re = 1 / 2 ∧ analyticOrderAt xi p = 1) ∧
      2 ^ k ∣ ∑ z ∈ t₁.filter (fun z => 1 / 2 < z.re), m₁ z := by
  have hEM : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖z‖ * (M : ℝ) ^ (-z.re) / z.re + ‖emCarrier M z - gN N z‖ < ‖gN N z‖ := by
    intro z hz
    exact lt_of_le_of_lt (add_le_add (hE z hz) (hclose z hz)) (hF z hz)
  exact xi_simple_window_and_rung_of_em_two_sign_data k hM h0 hrR hm₁ hcl₁ hstrip₂
    hm₂ hcl₂ hρ₁ hρ₂ hh hh0 hh' hh0' hfact₁ hfact₂ hchartStrip hEM
    hmono₁ hsign₁ hseg₁ hcount₂₁ hmono₂ hsign₂ hseg₂ hcount₂₂

end RHTower

namespace RHTower

open Complex Metric

/-- **Raw relative two-sign parity certificate.** Relative `η < 1` closeness plus
raw finite-carrier nonvanishing and two sign tables discharge the seam `hL`
congruence and prove the ANNEAL right-half window-count congruence, while retaining
the U0 principal-log correction bound. -/
theorem xi_window_parity_of_relative_two_sign_data_gN_nonzero {N : ℕ} (k : ℕ)
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ} {h h' : ℂ → ℂ} {a : ℂ} {r₀ R η : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R) (hη : η < 1)
    (hchartStrip : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, 0 < z.re ∧ z ≠ 1)
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hstrip₂ : ∀ z ∈ t₂, 0 < z.re ∧ z.re < 1)
    (hm₂ : ∀ z ∈ t₂, (m₂ z : ℕ∞) = analyticOrderAt (completedGN N) z)
    (hcl₂ : ∀ z ∈ t₂, lineReflect z ∈ t₂)
    (hρ₁ : ∀ w ∈ t₁, ‖w - a‖ ≤ r₀) (hρ₂ : ∀ w ∈ t₂, ‖w - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball a R)) (hh0' : ∀ z ∈ ball a R, h' z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    (hfact₂ : ∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h' z)
    (hgN0 : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, gN N z ≠ 0)
    (hrel : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖(xi z - completedGN N z) / completedGN N z‖ ≤ η)
    {s₁ : ℕ} {ts₁ : ℕ → ℝ}
    (hmono₁ : ∀ i, i < s₁ → ts₁ i < ts₁ (i + 1))
    (hsign₁ : ∀ i, i < s₁ →
      (xi (linePoint (ts₁ i))).re * (xi (linePoint (ts₁ (i + 1)))).re < 0)
    (hseg₁ : ∀ u : ℝ, ts₁ 0 ≤ u → u ≤ ts₁ s₁ → linePoint u ∈ ball a R)
    (hcount₂₁ : ∑ z ∈ t₂, m₂ z ≤ s₁)
    {s₂ : ℕ} {ts₂ : ℕ → ℝ}
    (hmono₂ : ∀ i, i < s₂ → ts₂ i < ts₂ (i + 1))
    (hsign₂ : ∀ i, i < s₂ →
      (completedGN N (linePoint (ts₂ i))).re *
        (completedGN N (linePoint (ts₂ (i + 1)))).re < 0)
    (hseg₂ : ∀ u : ℝ, ts₂ 0 ≤ u → u ≤ ts₂ s₂ → linePoint u ∈ ball a R)
    (hcount₂₂ : ∑ z ∈ t₂, m₂ z ≤ s₂) :
    (∑ z ∈ t₁.filter (fun z => 1 / 2 < z.re), m₁ z
      ≡ ∑ z ∈ t₂.filter (fun z => 1 / 2 < z.re), m₂ z [MOD 2 ^ k]) ∧
      ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
        ‖Complex.log (xi z / completedGN N z)‖ ≤
          (1 - η)⁻¹ * ‖(xi z - completedGN N z) / completedGN N z‖ := by
  have hG0 : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, completedGN N z ≠ 0 := by
    intro z hz
    obtain ⟨hσ, hz1⟩ := hchartStrip z hz
    exact completedGN_ne_zero_of_gN_ne_zero hσ hz1 (hgN0 z hz)
  have hdom : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖xi z - completedGN N z‖ < ‖completedGN N z‖ := by
    intro z hz
    have hzrel := hrel z hz
    rw [norm_div] at hzrel
    have hpos : 0 < ‖completedGN N z‖ := norm_pos_iff.mpr (hG0 z hz)
    have hmul := mul_le_mul_of_nonneg_right hzrel (le_of_lt hpos)
    rw [div_mul_cancel₀ _ hpos.ne'] at hmul
    exact lt_of_le_of_lt hmul (by simpa using mul_lt_mul_of_pos_right hη hpos)
  have hLeq : ∑ z ∈ t₁.filter (fun z => z.re = 1 / 2), m₁ z
      = ∑ z ∈ t₂.filter (fun z => z.re = 1 / 2), m₂ z :=
    hL_exact_of_two_sign_data h0 hrR hm₁ hcl₁ hstrip₂ hm₂ hcl₂ hρ₁ hρ₂
      hh hh0 hh' hh0' hfact₁ hfact₂ hdom hmono₁ hsign₁ hseg₁ hcount₂₁
      hmono₂ hsign₂ hseg₂ hcount₂₂
  have hL : ∑ z ∈ t₁.filter (fun z => z.re = 1 / 2), m₁ z
      ≡ ∑ z ∈ t₂.filter (fun z => z.re = 1 / 2), m₂ z [MOD 2 ^ (k + 1)] := by
    rw [hLeq]
  exact anneal_window_parity_transport_of_relative_close_gN_nonzero k h0 hrR hη
    hchartStrip hm₁ hcl₁ hstrip₂ hm₂ hcl₂ hρ₁ hρ₂ hh hh0 hh' hh0' hfact₁ hfact₂
    hgN0 hrel hL

/-- **Raw relative two-sign joint certificate.** Relative `η < 1` closeness plus raw
finite-carrier nonvanishing, a ξ sign table, and a completed-carrier sign table certify
both ξ on-line simplicity and the ξ dyadic rung; the seam congruence and finite-side
rung are derived from the same sign data. -/
theorem xi_simple_window_and_rung_of_relative_two_sign_data_gN_nonzero {N : ℕ} (k : ℕ)
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ} {h h' : ℂ → ℂ} {a : ℂ} {r₀ R η : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R) (hη : η < 1)
    (hchartStrip : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, 0 < z.re ∧ z ≠ 1)
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hstrip₂ : ∀ z ∈ t₂, 0 < z.re ∧ z.re < 1)
    (hm₂ : ∀ z ∈ t₂, (m₂ z : ℕ∞) = analyticOrderAt (completedGN N) z)
    (hcl₂ : ∀ z ∈ t₂, lineReflect z ∈ t₂)
    (hρ₁ : ∀ w ∈ t₁, ‖w - a‖ ≤ r₀) (hρ₂ : ∀ w ∈ t₂, ‖w - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball a R)) (hh0' : ∀ z ∈ ball a R, h' z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    (hfact₂ : ∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h' z)
    (hgN0 : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, gN N z ≠ 0)
    (hrel : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖(xi z - completedGN N z) / completedGN N z‖ ≤ η)
    {s₁ : ℕ} {ts₁ : ℕ → ℝ}
    (hmono₁ : ∀ i, i < s₁ → ts₁ i < ts₁ (i + 1))
    (hsign₁ : ∀ i, i < s₁ →
      (xi (linePoint (ts₁ i))).re * (xi (linePoint (ts₁ (i + 1)))).re < 0)
    (hseg₁ : ∀ u : ℝ, ts₁ 0 ≤ u → u ≤ ts₁ s₁ → linePoint u ∈ ball a R)
    (hcount₂₁ : ∑ z ∈ t₂, m₂ z ≤ s₁)
    {s₂ : ℕ} {ts₂ : ℕ → ℝ}
    (hmono₂ : ∀ i, i < s₂ → ts₂ i < ts₂ (i + 1))
    (hsign₂ : ∀ i, i < s₂ →
      (completedGN N (linePoint (ts₂ i))).re *
        (completedGN N (linePoint (ts₂ (i + 1)))).re < 0)
    (hseg₂ : ∀ u : ℝ, ts₂ 0 ≤ u → u ≤ ts₂ s₂ → linePoint u ∈ ball a R)
    (hcount₂₂ : ∑ z ∈ t₂, m₂ z ≤ s₂) :
    (∀ p ∈ ball a R, xi p = 0 → p.re = 1 / 2 ∧ analyticOrderAt xi p = 1) ∧
      (2 ^ k ∣ ∑ z ∈ t₁.filter (fun z => 1 / 2 < z.re), m₁ z) ∧
        ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
          ‖Complex.log (xi z / completedGN N z)‖ ≤
            (1 - η)⁻¹ * ‖(xi z - completedGN N z) / completedGN N z‖ := by
  have hsimple :=
    xi_window_simple_online_of_relative_sign_certificate_gN_nonzero h0 hrR hη hchartStrip
      hm₁ hcl₁ hρ₁ hρ₂ hh hh0 hh' hh0' hfact₁ hfact₂ hgN0 hrel
      hmono₁ hsign₁ hseg₁ hcount₂₁
  obtain ⟨hparity, hlog⟩ :=
    xi_window_parity_of_relative_two_sign_data_gN_nonzero k h0 hrR hη hchartStrip
      hm₁ hcl₁ hstrip₂ hm₂ hcl₂ hρ₁ hρ₂ hh hh0 hh' hh0' hfact₁ hfact₂ hgN0 hrel
      hmono₁ hsign₁ hseg₁ hcount₂₁ hmono₂ hsign₂ hseg₂ hcount₂₂
  obtain ⟨-, hfin_zero⟩ :=
    completedGN_window_online_of_sign_data hstrip₂ hm₂ hcl₂ hh0' hfact₂
      hmono₂ hsign₂ hseg₂ hcount₂₂
  have hfin : 2 ^ k ∣ ∑ z ∈ t₂.filter (fun z => 1 / 2 < z.re), m₂ z := by
    rw [hfin_zero]
    exact dvd_zero _
  have hrung : 2 ^ k ∣ ∑ z ∈ t₁.filter (fun z => 1 / 2 < z.re), m₁ z :=
    Nat.modEq_zero_iff_dvd.mp (hparity.trans (Nat.modEq_zero_iff_dvd.mpr hfin))
  exact ⟨hsimple.1, hrung, hlog⟩

/-- **LOW-floor relative two-sign joint certificate.** A nonnegative LOW floor
discharges the finite-carrier nonvanishing side condition in the relative two-sign
joint certificate, while preserving the same ξ simplicity, dyadic rung, and U0 log
control conclusions. -/
theorem xi_simple_window_and_rung_of_relative_two_sign_data_carrierFloorOn {N : ℕ}
    (k : ℕ)
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ} {h h' : ℂ → ℂ} {a : ℂ}
    {r₀ R η ε : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R) (hη : η < 1) (hε : 0 ≤ ε)
    (hF : CarrierFloorOn (chartRA a r₀ R ∪ chartLA a r₀ R) N ε)
    (hchartStrip : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, 0 < z.re ∧ z ≠ 1)
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hstrip₂ : ∀ z ∈ t₂, 0 < z.re ∧ z.re < 1)
    (hm₂ : ∀ z ∈ t₂, (m₂ z : ℕ∞) = analyticOrderAt (completedGN N) z)
    (hcl₂ : ∀ z ∈ t₂, lineReflect z ∈ t₂)
    (hρ₁ : ∀ w ∈ t₁, ‖w - a‖ ≤ r₀) (hρ₂ : ∀ w ∈ t₂, ‖w - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball a R)) (hh0' : ∀ z ∈ ball a R, h' z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    (hfact₂ : ∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h' z)
    (hrel : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖(xi z - completedGN N z) / completedGN N z‖ ≤ η)
    {s₁ : ℕ} {ts₁ : ℕ → ℝ}
    (hmono₁ : ∀ i, i < s₁ → ts₁ i < ts₁ (i + 1))
    (hsign₁ : ∀ i, i < s₁ →
      (xi (linePoint (ts₁ i))).re * (xi (linePoint (ts₁ (i + 1)))).re < 0)
    (hseg₁ : ∀ u : ℝ, ts₁ 0 ≤ u → u ≤ ts₁ s₁ → linePoint u ∈ ball a R)
    (hcount₂₁ : ∑ z ∈ t₂, m₂ z ≤ s₁)
    {s₂ : ℕ} {ts₂ : ℕ → ℝ}
    (hmono₂ : ∀ i, i < s₂ → ts₂ i < ts₂ (i + 1))
    (hsign₂ : ∀ i, i < s₂ →
      (completedGN N (linePoint (ts₂ i))).re *
        (completedGN N (linePoint (ts₂ (i + 1)))).re < 0)
    (hseg₂ : ∀ u : ℝ, ts₂ 0 ≤ u → u ≤ ts₂ s₂ → linePoint u ∈ ball a R)
    (hcount₂₂ : ∑ z ∈ t₂, m₂ z ≤ s₂) :
    (∀ p ∈ ball a R, xi p = 0 → p.re = 1 / 2 ∧ analyticOrderAt xi p = 1) ∧
      (2 ^ k ∣ ∑ z ∈ t₁.filter (fun z => 1 / 2 < z.re), m₁ z) ∧
        ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
          ‖Complex.log (xi z / completedGN N z)‖ ≤
            (1 - η)⁻¹ * ‖(xi z - completedGN N z) / completedGN N z‖ := by
  have hgN0 : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, gN N z ≠ 0 :=
    gN_ne_zero_of_carrierFloorOn hε hF
  exact xi_simple_window_and_rung_of_relative_two_sign_data_gN_nonzero k h0 hrR hη
    hchartStrip hm₁ hcl₁ hstrip₂ hm₂ hcl₂ hρ₁ hρ₂ hh hh0 hh' hh0'
    hfact₁ hfact₂ hgN0 hrel hmono₁ hsign₁ hseg₁ hcount₂₁
    hmono₂ hsign₂ hseg₂ hcount₂₂

end RHTower

namespace RHTower

open Complex Metric

/-- Finite-data half-floor two-sign certificate.  EM remainder control, finite
carrier closeness, and a doubled LOW floor supply the relative `1/2` error and
finite-carrier nonvanishing needed by the strongest two-sign window/rung endpoint. -/
theorem xi_simple_window_and_rung_of_emCarrier_close_half_floor_two_sign_data
    {N M : ℕ} (k : ℕ) (hM : 1 ≤ M)
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ} {h h' : ℂ → ℂ} {a : ℂ}
    {r₀ R ε₁ δ : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R) (hεδ : 0 ≤ ε₁ + δ)
    (hchartStrip : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, 0 < z.re ∧ z ≠ 1)
    (hE : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
    (hclose : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖emCarrier M z - gN N z‖ ≤ δ)
    (hF : CarrierFloorOn (chartRA a r₀ R ∪ chartLA a r₀ R) N (2 * (ε₁ + δ)))
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hstrip₂ : ∀ z ∈ t₂, 0 < z.re ∧ z.re < 1)
    (hm₂ : ∀ z ∈ t₂, (m₂ z : ℕ∞) = analyticOrderAt (completedGN N) z)
    (hcl₂ : ∀ z ∈ t₂, lineReflect z ∈ t₂)
    (hρ₁ : ∀ w ∈ t₁, ‖w - a‖ ≤ r₀) (hρ₂ : ∀ w ∈ t₂, ‖w - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball a R)) (hh0' : ∀ z ∈ ball a R, h' z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    (hfact₂ : ∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h' z)
    {s₁ : ℕ} {ts₁ : ℕ → ℝ}
    (hmono₁ : ∀ i, i < s₁ → ts₁ i < ts₁ (i + 1))
    (hsign₁ : ∀ i, i < s₁ →
      (xi (linePoint (ts₁ i))).re * (xi (linePoint (ts₁ (i + 1)))).re < 0)
    (hseg₁ : ∀ u : ℝ, ts₁ 0 ≤ u → u ≤ ts₁ s₁ → linePoint u ∈ ball a R)
    (hcount₂₁ : ∑ z ∈ t₂, m₂ z ≤ s₁)
    {s₂ : ℕ} {ts₂ : ℕ → ℝ}
    (hmono₂ : ∀ i, i < s₂ → ts₂ i < ts₂ (i + 1))
    (hsign₂ : ∀ i, i < s₂ →
      (completedGN N (linePoint (ts₂ i))).re *
        (completedGN N (linePoint (ts₂ (i + 1)))).re < 0)
    (hseg₂ : ∀ u : ℝ, ts₂ 0 ≤ u → u ≤ ts₂ s₂ → linePoint u ∈ ball a R)
    (hcount₂₂ : ∑ z ∈ t₂, m₂ z ≤ s₂) :
    (∀ p ∈ ball a R, xi p = 0 → p.re = 1 / 2 ∧ analyticOrderAt xi p = 1) ∧
      (2 ^ k ∣ ∑ z ∈ t₁.filter (fun z => 1 / 2 < z.re), m₁ z) ∧
        ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
          ‖Complex.log (xi z / completedGN N z)‖ ≤
            (1 - (1 / 2 : ℝ))⁻¹ * ‖(xi z - completedGN N z) / completedGN N z‖ := by
  have hη : (1 / 2 : ℝ) < 1 := by norm_num
  have hfloor_nonneg : 0 ≤ 2 * (ε₁ + δ) := mul_nonneg (by norm_num) hεδ
  have hrel : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖(xi z - completedGN N z) / completedGN N z‖ ≤ (1 / 2 : ℝ) :=
    completed_relative_error_of_emCarrier_close_half_floor hM hεδ hchartStrip hE hclose hF
  exact xi_simple_window_and_rung_of_relative_two_sign_data_carrierFloorOn k h0 hrR hη
    hfloor_nonneg hF hchartStrip hm₁ hcl₁ hstrip₂ hm₂ hcl₂ hρ₁ hρ₂ hh hh0 hh' hh0'
    hfact₁ hfact₂ hrel
    hmono₁ hsign₁ hseg₁ hcount₂₁ hmono₂ hsign₂ hseg₂ hcount₂₂

end RHTower
