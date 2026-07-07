/-
The finite carrier's hole-zero disposition at a dominated annulus: the count
identity in configuration form, the parity from one circle, and the negation
surface.

Any member dominating ξ on the charts of an isolating annulus has total
enclosed multiplicity equal to the central ξ-order — the count identity carried
from list splits to indexed configurations with multiplicities.  The parity of
the count is forced by domination on ONE interior circle alone: the boundary
trace holonomies of the two members must agree, and each computes its own
count.  At a strip point of odd ξ-order, dominating splits of the completed
Euler–Maclaurin member exist unconditionally and every one of them has an odd
hole count: the finite carrier's hole-zero disposition is the surface on which
the base rung is decided.
-/
import GaloisForLFunctions.RHTower.CertificateActivation

noncomputable section

namespace RHTower

open Complex Metric Set

/-! ### §1 Indexed configurations as list splits -/

/-- The list of an indexed configuration: each centre repeated with its
multiplicity. -/
def configList {ι : Type*} (s : Finset ι) (ρc : ι → ℂ) (m : ι → ℕ) : List ℂ :=
  s.toList.flatMap fun i => List.replicate (m i) (ρc i)

theorem configList_length {ι : Type*} (s : Finset ι) (ρc : ι → ℂ) (m : ι → ℕ) :
    (configList s ρc m).length = ∑ i ∈ s, m i := by
  rw [configList, List.length_flatMap]
  simp only [List.length_replicate]
  exact Finset.sum_map_toList s m

theorem configList_map_prod {ι : Type*} (s : Finset ι) (ρc : ι → ℂ) (m : ι → ℕ)
    (z : ℂ) :
    ((configList s ρc m).map (fun w => z - w)).prod
      = ∏ i ∈ s, (z - ρc i) ^ m i := by
  rw [configList, List.map_flatMap, ← Finset.prod_map_toList]
  induction s.toList with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.prod_append, List.map_cons,
      List.prod_cons, List.map_replicate, List.prod_replicate]
    rw [← ih]
    simp [List.map_replicate]

theorem configList_mem {ι : Type*} {s : Finset ι} {ρc : ι → ℂ} {m : ι → ℕ}
    {ρ : ℂ} {r₀ : ℝ} (hρ : ∀ i ∈ s, ‖ρc i - ρ‖ ≤ r₀) :
    ∀ w ∈ configList s ρc m, ‖w - ρ‖ ≤ r₀ := by
  intro w hw
  rw [configList, List.mem_flatMap] at hw
  obtain ⟨i, hi, hwi⟩ := hw
  obtain ⟨-, rfl⟩ := List.mem_replicate.mp hwi
  exact hρ i (Finset.mem_toList.mp hi)

/-! ### §2 The count identity in configuration form -/

/-- **The count identity, configuration form**: the total multiplicity of any
enclosed configuration of any member dominating ξ on the charts of an isolating
annulus is the central ξ-order. -/
theorem enclosed_configuration_count_of_domination {ι : Type*} (s : Finset ι)
    (ρc : ι → ℂ) (m : ι → ℕ) {F u : ℂ → ℂ} {ρ : ℂ} {r₀ R : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hiso : ∀ z ∈ ball ρ R, z ≠ ρ → xi z ≠ 0)
    (hρ : ∀ i ∈ s, ‖ρc i - ρ‖ ≤ r₀)
    (hu_an : AnalyticOnNhd ℂ u (ball ρ R)) (hu_ne : ∀ z ∈ ball ρ R, u z ≠ 0)
    (hfact : ∀ z ∈ chartRA ρ r₀ R ∪ chartLA ρ r₀ R,
      F z = (∏ i ∈ s, (z - ρc i) ^ m i) * u z)
    (hdom : ∀ z ∈ chartRA ρ r₀ R ∪ chartLA ρ r₀ R, ‖xi z - F z‖ < ‖F z‖) :
    (analyticOrderAt xi ρ).toNat = ∑ i ∈ s, m i := by
  rw [← configList_length s ρc m]
  refine enclosed_count_eq_of_split_domination h0 hrR hiso hu_an hu_ne
    (configList_mem hρ) ?_ hdom
  intro z hz
  rw [hfact z hz, configList_map_prod]

/-! ### §3 The negation surface -/

/-- **The negation surface**: at a strip point of odd ξ-order, dominating splits
of the completed EM member exist unconditionally and EVERY one of them has an
odd hole count — the finite carrier's hole-zero disposition is the surface on
which the base rung is decided. -/
theorem emSplit_odd_count_at_odd_xi_order {ρ : ℂ}
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    {m : ℕ} (hm : analyticOrderAt xi ρ = m) (hodd : Odd m) :
    (∃ (r₀ R : ℝ) (N : ℕ) (zs : List ℂ) (u : ℂ → ℂ),
      EMSplitData ρ r₀ R N zs u) ∧
    ∀ (r₀ R : ℝ) (N : ℕ) (zs : List ℂ) (u : ℂ → ℂ),
      EMSplitData ρ r₀ R N zs u → Odd zs.length := by
  refine ⟨emSplitData_exists ρ h0 h1, ?_⟩
  intro r₀ R N zs u hdata
  have hc := emSplitData_count_eq hdata
  rw [hm, ENat.toNat_coe] at hc
  rw [← hc]
  exact hodd

/-! ### §4 The parity from one circle -/

theorem neg_one_pow_pm (k : ℕ) :
    ((-1 : ℂ)) ^ k = 1 ∨ ((-1 : ℂ)) ^ k = -1 := by
  rcases Nat.even_or_odd k with h | h
  · exact Or.inl h.neg_one_pow
  · exact Or.inr h.neg_one_pow

theorem odd_iff_of_neg_one_pow_eq {a b : ℕ}
    (h : ((-1 : ℂ)) ^ a = (-1) ^ b) : Odd a ↔ Odd b := by
  constructor
  · intro ha
    by_contra hb
    rw [Nat.not_odd_iff_even] at hb
    rw [ha.neg_one_pow, hb.neg_one_pow] at h
    norm_num at h
  · intro hb
    by_contra ha
    rw [Nat.not_odd_iff_even] at ha
    rw [ha.neg_one_pow, hb.neg_one_pow] at h
    norm_num at h

/-- **The count parity from ONE circle**: an enclosed configuration of a member
that dominates a function with an isolated zero of order `m` on a single
interior circle has total multiplicity of the parity of `m` — the boundary
trace holonomies must agree, and each computes its own count.  Strictly weaker
input than the chart-domination count identity: one circle of boundary data
already pins the parity. -/
theorem configuration_parity_of_circle_domination {ι : Type*} (s : Finset ι)
    (ρc : ι → ℂ) (mult : ι → ℕ) {g F h : ℂ → ℂ} {ρ : ℂ} {r₀ r R : ℝ}
    (h0 : 0 < r₀) (hr₀ : r₀ < r) (hrR : r < R)
    (hg : AnalyticOnNhd ℂ g (ball ρ R))
    (hiso : ∀ z ∈ ball ρ R, z ≠ ρ → g z ≠ 0)
    {m : ℕ} (hm : analyticOrderAt g ρ = m)
    (hρc : ∀ i ∈ s, ‖ρc i - ρ‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball ρ R)) (hh0 : ∀ z ∈ ball ρ R, h z ≠ 0)
    (hfact : ∀ z ∈ ball ρ R, F z = (∏ i ∈ s, (z - ρc i) ^ mult i) * h z)
    (hdom : ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
      ‖g (circleMap ρ r θ) - F (circleMap ρ r θ)‖
        < ‖F (circleMap ρ r θ)‖) :
    Odd (∑ i ∈ s, mult i) ↔ Odd m := by
  have h0' : (0 : ℝ) ≤ r₀ := le_of_lt h0
  -- nonvanishing of g and F on the annulus
  have hg0 : ∀ z ∈ ball ρ R \ closedBall ρ r₀, g z ≠ 0 := by
    intro z hz
    refine hiso z hz.1 fun heq => ?_
    exact hz.2 (by rw [heq, mem_closedBall, dist_self]; exact h0')
  have hfact' : ∀ z ∈ ball ρ R,
      F z = (∏ i ∈ s, (z - ρc i) ^ mult i) * h z := hfact
  have hF0 : ∀ z ∈ ball ρ R \ closedBall ρ r₀, F z ≠ 0 := by
    intro z hz hzero
    have hkey := enclosed_ne_zero_on_annulus' (f := fun z =>
      (∏ i ∈ s, (z - ρc i) ^ mult i) * h z) hρc hh0 (fun z _ => rfl) z hz
    rw [hfact z hz.1] at hzero
    exact hkey hzero
  have hFan : AnalyticOnNhd ℂ F (ball ρ R \ closedBall ρ r₀) := by
    intro z hz
    have hprod : AnalyticAt ℂ (fun w => ∏ i ∈ s, (w - ρc i) ^ mult i) z :=
      Finset.analyticAt_fun_prod s fun i _ =>
        (analyticAt_id.sub analyticAt_const).pow (mult i)
    refine (hprod.mul (hh z hz.1)).congr ?_
    filter_upwards [isOpen_ball.mem_nhds hz.1] with w hw
    exact (hfact w hw).symm
  -- the two traces
  obtain ⟨W, hWc, hWsq⟩ := exists_circle_trace h0 hr₀ hrR
    (fun z hz => hg z hz.1) hg0
  obtain ⟨V, hVc, hVsq⟩ := exists_circle_trace h0 hr₀ hrR hFan hF0
  -- the g-trace holonomy is (−1)^m
  obtain ⟨G₁, hG₁, hpG₁⟩ := exists_chartRA_sqrt h0 (lt_trans hr₀ hrR)
    (fun z hz => hg z hz.2.1) (fun z hz => hg0 z hz.2)
  obtain ⟨G₂, hG₂, hpG₂⟩ := exists_chartLA_sqrt h0 (lt_trans hr₀ hrR)
    (fun z hz => hg z hz.2.1) (fun z hz => hg0 z hz.2)
  have hWhol : W (3 * Real.pi / 2) = (-1) ^ m * W (-(Real.pi / 2)) :=
    trace_holonomy_isolated_zero h0' hr₀ hrR hg hiso hm hG₁ hG₂ hpG₁ hpG₂
      hWc hWsq
  -- the F-trace holonomy is (−1)^Σ
  obtain ⟨C₁, hC₁, hpC₁⟩ := exists_chartRA_sqrt h0 (lt_trans hr₀ hrR)
    (fun z hz => hFan z hz.2) (fun z hz => hF0 z hz.2)
  obtain ⟨C₂, hC₂, hpC₂⟩ := exists_chartLA_sqrt h0 (lt_trans hr₀ hrR)
    (fun z hz => hFan z hz.2) (fun z hz => hF0 z hz.2)
  have hVhol : V (3 * Real.pi / 2)
      = (-1) ^ (∑ i ∈ s, mult i) * V (-(Real.pi / 2)) :=
    continuous_trace_holonomy_neg_one_pow s ρc mult h0' hr₀ hrR hρc hh hh0
      hfact hC₁ hC₂ hpC₁ hpC₂ hVc hVsq
  -- transfer along the dominated circle
  have htransfer := holonomy_eq_of_circle_domination (f := F) (g := g)
    hVc hWc hVsq hWsq hdom hVhol hWhol
    (neg_one_pow_pm _) (neg_one_pow_pm _)
  exact (odd_iff_of_neg_one_pow_eq htransfer).symm

/-! ### §5 Product estimates for placements -/

/-- A product of factors each of norm at least `c ≥ 0` has norm at least
`c^length`. -/
theorem list_prod_norm_ge {l : List ℂ} {c : ℝ} (hc : 0 ≤ c)
    (hl : ∀ x ∈ l, c ≤ ‖x‖) : c ^ l.length ≤ ‖l.prod‖ := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.prod_cons, List.length_cons, pow_succ', norm_mul]
    exact mul_le_mul (hl x List.mem_cons_self)
      (ih fun y hy => hl y (List.mem_cons_of_mem x hy))
      (pow_nonneg hc _) (norm_nonneg _)

/-- A product of factors each of norm at most `M` has norm at most
`M^length`. -/
theorem list_prod_norm_le {l : List ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hl : ∀ x ∈ l, ‖x‖ ≤ M) : ‖l.prod‖ ≤ M ^ l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.prod_cons, List.length_cons, pow_succ', norm_mul]
    exact mul_le_mul (hl x List.mem_cons_self)
      (ih fun y hy => hl y (List.mem_cons_of_mem x hy))
      (norm_nonneg _) hM

/-- **Telescoping product difference**: componentwise `ε`-close factor lists of
common norm bound `M` have products within `n·ε·M^(n−1)`. -/
theorem list_prod_sub_prod_norm_le {l : List (ℂ × ℂ)} {M ε : ℝ}
    (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (hfst : ∀ p ∈ l, ‖p.1‖ ≤ M) (hsnd : ∀ p ∈ l, ‖p.2‖ ≤ M)
    (hdiff : ∀ p ∈ l, ‖p.1 - p.2‖ ≤ ε) :
    ‖(l.map Prod.fst).prod - (l.map Prod.snd).prod‖
      ≤ l.length * ε * M ^ (l.length - 1) := by
  induction l with
  | nil => simp
  | cons p l ih =>
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons]
    have hkey : p.1 * (l.map Prod.fst).prod - p.2 * (l.map Prod.snd).prod
        = (p.1 - p.2) * (l.map Prod.fst).prod
          + p.2 * ((l.map Prod.fst).prod - (l.map Prod.snd).prod) := by
      ring
    rw [hkey]
    have hA : ‖(l.map Prod.fst).prod‖ ≤ M ^ l.length := by
      have h := list_prod_norm_le (l := l.map Prod.fst) (M := M) hM ?side
      case side =>
        intro x hx
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
        exact hfst q (List.mem_cons_of_mem p hq)
      rwa [List.length_map] at h
    have hAB := ih (fun q hq => hfst q (List.mem_cons_of_mem p hq))
      (fun q hq => hsnd q (List.mem_cons_of_mem p hq))
      (fun q hq => hdiff q (List.mem_cons_of_mem p hq))
    have hstep : ‖(p.1 - p.2) * (l.map Prod.fst).prod
          + p.2 * ((l.map Prod.fst).prod - (l.map Prod.snd).prod)‖
        ≤ ε * M ^ l.length + M * (l.length * ε * M ^ (l.length - 1)) := by
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, norm_mul]
      exact add_le_add
        (mul_le_mul (hdiff p List.mem_cons_self) hA (norm_nonneg _) hε)
        (mul_le_mul (hsnd p List.mem_cons_self) hAB (norm_nonneg _) hM)
    refine le_trans hstep ?_
    have harith : ∀ k : ℕ, ε * M ^ k + M * (k * ε * M ^ (k - 1))
        ≤ ((k : ℝ) + 1) * ε * M ^ k := by
      intro k
      cases k with
      | zero => simp
      | succ k' =>
        have hMM : M * M ^ (k' + 1 - 1) = M ^ (k' + 1) := by
          rw [Nat.add_sub_cancel, ← pow_succ']
        push_cast
        refine le_of_eq ?_
        calc ε * M ^ (k' + 1) + M * (((k' : ℝ) + 1) * ε * M ^ (k' + 1 - 1))
            = ε * M ^ (k' + 1)
              + ((k' : ℝ) + 1) * ε * (M * M ^ (k' + 1 - 1)) := by ring
          _ = ε * M ^ (k' + 1) + ((k' : ℝ) + 1) * ε * M ^ (k' + 1) := by
              rw [hMM]
          _ = (((k' : ℝ) + 1) + 1) * ε * M ^ (k' + 1) := by ring
    have hfin := harith l.length
    rw [List.length_cons, Nat.add_sub_cancel]
    push_cast
    exact hfin

/-! ### §6 Realizability: positions in the hole are free -/

/-- **Realizability**: every hole-confined placement with the polynomial
smallness margin is the zero list of a member dominating on the whole annulus —
built from the peel cofactor of the dominated function itself.  The placement's
positions are arbitrary within the inner hole; only the count enters the
margin. -/
theorem exists_dominating_split_of_configuration {g : ℂ → ℂ} {ρ : ℂ}
    {r₀ r₁ R : ℝ} (h0 : 0 ≤ r₀) (hrR : r₀ < R) (hr₁0 : 0 ≤ r₁) (hr₁ : r₁ < r₀)
    (hg : AnalyticOnNhd ℂ g (ball ρ R))
    (hiso : ∀ z ∈ ball ρ R, z ≠ ρ → g z ≠ 0)
    {m : ℕ} (hm : analyticOrderAt g ρ = m)
    (zs : List ℂ) (hzs : ∀ w ∈ zs, ‖w - ρ‖ ≤ r₁) (hlen : zs.length = m)
    (hsmall : (m : ℝ) * r₁ * (R + r₁) ^ (m - 1) < (r₀ - r₁) ^ m) :
    ∃ u : ℂ → ℂ, AnalyticOnNhd ℂ u (ball ρ R) ∧ (∀ z ∈ ball ρ R, u z ≠ 0) ∧
      ∀ z ∈ chartRA ρ r₀ R ∪ chartLA ρ r₀ R,
        ‖g z - ((zs.map (fun w => z - w)).prod) * u z‖
          < ‖((zs.map (fun w => z - w)).prod) * u z‖ := by
  have hR : 0 < R := lt_of_le_of_lt h0 hrR
  obtain ⟨h, hhan, hhρ, hfact, -⟩ := exists_peel isOpen_ball hg
    (mem_ball_self hR) hm
  have hh0 : ∀ z ∈ ball ρ R, h z ≠ 0 := by
    intro z hz
    by_cases hzρ : z = ρ
    · rw [hzρ]
      exact hhρ
    · intro hzero
      have hfz := hfact z hz
      rw [hzero, mul_zero] at hfz
      exact hiso z hz hzρ hfz
  refine ⟨h, hhan, hh0, ?_⟩
  intro z hz
  rw [charts_union_eq_annulus ρ h0] at hz
  have hzball : z ∈ ball ρ R := hz.1
  have ht : r₀ < ‖z - ρ‖ := by
    have := hz.2
    rwa [mem_closedBall, dist_eq_norm, not_le] at this
  have htR : ‖z - ρ‖ < R := by
    have := hz.1
    rwa [mem_ball, dist_eq_norm] at this
  -- factor bounds on the circle of `z`
  have hfacB : ∀ w ∈ zs, ‖z - w‖ ≤ R + r₁ := by
    intro w hw
    calc ‖z - w‖ = ‖(z - ρ) - (w - ρ)‖ := by ring_nf
      _ ≤ ‖z - ρ‖ + ‖w - ρ‖ := norm_sub_le _ _
      _ ≤ R + r₁ := add_le_add (le_of_lt htR) (hzs w hw)
  have hfacLo : ∀ w ∈ zs, r₀ - r₁ ≤ ‖z - w‖ := by
    intro w hw
    have htri : ‖z - ρ‖ ≤ ‖z - w‖ + ‖w - ρ‖ := by
      calc ‖z - ρ‖ = ‖(z - w) + (w - ρ)‖ := by ring_nf
        _ ≤ ‖z - w‖ + ‖w - ρ‖ := norm_add_le _ _
    have := hzs w hw
    linarith
  -- the pair list and the two products
  set P : ℂ := (zs.map (fun w => z - w)).prod with hPdef
  have hPlow : (r₀ - r₁) ^ m ≤ ‖P‖ := by
    have h1 := list_prod_norm_ge (l := zs.map (fun w => z - w))
      (c := r₀ - r₁) (by linarith) ?side
    case side =>
      intro x hx
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
      exact hfacLo w hw
    rwa [List.length_map, hlen] at h1
  have hdiffbound : ‖P - (z - ρ) ^ m‖
      ≤ (m : ℝ) * r₁ * (R + r₁) ^ (m - 1) := by
    have hbig := list_prod_sub_prod_norm_le
      (l := zs.map (fun w => (z - w, z - ρ))) (M := R + r₁) (ε := r₁)
      (by linarith) hr₁0 ?f1 ?f2 ?f3
    case f1 =>
      intro p hp
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hp
      exact hfacB w hw
    case f2 =>
      intro p hp
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hp
      calc ‖z - ρ‖ ≤ R := le_of_lt htR
        _ ≤ R + r₁ := by linarith
    case f3 =>
      intro p hp
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hp
      calc ‖(z - w) - (z - ρ)‖ = ‖ρ - w‖ := by ring_nf
        _ = ‖w - ρ‖ := by rw [norm_sub_rev]
        _ ≤ r₁ := hzs w hw
    rw [List.map_map, List.map_map] at hbig
    have hfsteq : (Prod.fst ∘ fun w => ((z - w : ℂ), (z - ρ : ℂ)))
        = fun w => z - w := rfl
    have hsndeq : (Prod.snd ∘ fun w => ((z - w : ℂ), (z - ρ : ℂ)))
        = fun _ => z - ρ := rfl
    rw [hfsteq, hsndeq, List.map_const', List.prod_replicate,
      List.length_map, hlen] at hbig
    exact hbig
  -- assemble the strict domination
  have hgz : g z = (z - ρ) ^ m * h z := hfact z hzball
  have hkey : g z - P * h z = ((z - ρ) ^ m - P) * h z := by
    rw [hgz]
    ring
  have hhz : 0 < ‖h z‖ := norm_pos_iff.mpr (hh0 z hzball)
  rw [hkey, norm_mul, norm_mul]
  refine mul_lt_mul_of_pos_right ?_ hhz
  calc ‖(z - ρ) ^ m - P‖ = ‖P - (z - ρ) ^ m‖ := norm_sub_rev _ _
    _ ≤ (m : ℝ) * r₁ * (R + r₁) ^ (m - 1) := hdiffbound
    _ < (r₀ - r₁) ^ m := hsmall
    _ ≤ ‖P‖ := hPlow

/-- A placement product is continuous in the variable. -/
theorem continuous_placement_prod (zs : List ℂ) :
    Continuous fun z : ℂ => ((zs.map (fun w' => z - w')).prod) := by
  induction zs with
  | nil => simpa using continuous_const
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (continuous_id.sub continuous_const).mul ih

/-- **Open-hole confinement**: the zeros of any split-form member dominating ξ
on the charts lie STRICTLY inside the hole — a placement touching the hole
boundary is incompatible with domination, whatever the cofactor: approaching
the boundary zero through the annulus drives the member to zero while ξ holds
its floor. -/
theorem dominating_split_zeros_lt_hole {ρ : ℂ} {r₀ R : ℝ}
    (h0 : 0 < r₀) (hrR : r₀ < R)
    (hiso : ∀ z ∈ ball ρ R, z ≠ ρ → xi z ≠ 0)
    {zs : List ℂ} {u : ℂ → ℂ}
    (hu_an : AnalyticOnNhd ℂ u (ball ρ R))
    (hzs : ∀ w ∈ zs, ‖w - ρ‖ ≤ r₀)
    (hdom : ∀ z ∈ chartRA ρ r₀ R ∪ chartLA ρ r₀ R,
      ‖xi z - ((zs.map (fun w => z - w)).prod) * u z‖
        < ‖((zs.map (fun w => z - w)).prod) * u z‖) :
    ∀ w ∈ zs, ‖w - ρ‖ < r₀ := by
  intro w hw
  rcases lt_or_eq_of_le (hzs w hw) with h | heq
  · exact h
  · exfalso
    have hwρ : w ≠ ρ := by
      intro hcontra
      rw [hcontra, sub_self, norm_zero] at heq
      exact absurd heq.symm (ne_of_gt h0)
    have hwball : w ∈ ball ρ R := by
      rw [mem_ball, dist_eq_norm, heq]
      exact hrR
    set ray : ℝ → ℂ := fun δ => ρ + ((1 + δ : ℝ) : ℂ) * (w - ρ) with hray_def
    have hray : Filter.Tendsto ray (nhdsWithin 0 (Ioi 0)) (nhds w) := by
      have hcont : Filter.Tendsto ray
          (nhds 0) (nhds (ρ + ((1 + 0 : ℝ) : ℂ) * (w - ρ))) := by
        apply Filter.Tendsto.add tendsto_const_nhds
        apply Filter.Tendsto.mul_const
        exact (Complex.continuous_ofReal.comp
          (continuous_const.add continuous_id)).tendsto 0
      rw [show ρ + ((1 + 0 : ℝ) : ℂ) * (w - ρ) = w by push_cast; ring] at hcont
      exact hcont.mono_left nhdsWithin_le_nhds
    have hraymem : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Ioi 0),
        ray δ ∈ chartRA ρ r₀ R ∪ chartLA ρ r₀ R := by
      filter_upwards [Ioo_mem_nhdsGT
        (show (0 : ℝ) < R / r₀ - 1 by
          rw [lt_sub_iff_add_lt, zero_add, lt_div_iff₀ h0, one_mul]
          exact hrR)] with δ hδ
      rw [charts_union_eq_annulus ρ (le_of_lt h0)]
      have hnorm : ‖ray δ - ρ‖ = (1 + δ) * r₀ := by
        rw [show ray δ - ρ = ((1 + δ : ℝ) : ℂ) * (w - ρ) by
          rw [hray_def]; ring, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, heq, abs_of_pos (by linarith [hδ.1])]
      constructor
      · rw [mem_ball, dist_eq_norm, hnorm]
        have h2 := hδ.2
        rw [lt_sub_iff_add_lt] at h2
        calc (1 + δ) * r₀ < (R / r₀) * r₀ := by
              apply mul_lt_mul_of_pos_right _ h0
              linarith
          _ = R := by field_simp
      · intro hmem
        rw [mem_closedBall, dist_eq_norm, hnorm] at hmem
        nlinarith [hδ.1]
    -- the member vanishes at `w`; ξ does not
    have hG0 : ((zs.map (fun w' => w - w')).prod : ℂ) * u w = 0 := by
      rw [List.prod_eq_zero (List.mem_map.mpr ⟨w, hw, by rw [sub_self]⟩),
        zero_mul]
    have hGat : ContinuousAt (fun z : ℂ =>
        ((zs.map (fun w' => z - w')).prod) * u z) w :=
      (continuous_placement_prod zs).continuousAt.mul
        (hu_an w hwball).continuousAt
    have hxiat : ContinuousAt xi w := xi_differentiable.continuous.continuousAt
    have hφ : Filter.Tendsto
        (fun δ => ‖xi (ray δ)
            - ((zs.map (fun w' => ray δ - w')).prod) * u (ray δ)‖
          - ‖((zs.map (fun w' => ray δ - w')).prod) * u (ray δ)‖)
        (nhdsWithin 0 (Ioi 0)) (nhds (‖xi w‖)) := by
      have hGtend := (hGat.tendsto.comp hray)
      rw [hG0] at hGtend
      have hxitend := hxiat.tendsto.comp hray
      have h1 := ((hxitend.sub hGtend).norm).sub hGtend.norm
      simpa using h1
    have hev : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Ioi 0),
        ‖xi (ray δ)
            - ((zs.map (fun w' => ray δ - w')).prod) * u (ray δ)‖
          - ‖((zs.map (fun w' => ray δ - w')).prod) * u (ray δ)‖ ≤ 0 := by
      filter_upwards [hraymem] with δ hδ
      have := hdom (ray δ) hδ
      linarith
    have hle : ‖xi w‖ ≤ 0 := le_of_tendsto hφ hev
    have hxiw : xi w = 0 := norm_le_zero_iff.mp hle
    exact hiso w hwball hwρ hxiw

/-- **The central placement always realizes**: `m` copies of the centre form
the zero list of a dominating member on every isolating annulus — the smallness
margin is vacuous at inner radius zero, so the compatible set is nonempty for
every geometry. -/
theorem exists_dominating_split_central {g : ℂ → ℂ} {ρ : ℂ} {r₀ R : ℝ}
    (h0 : 0 < r₀) (hrR : r₀ < R)
    (hg : AnalyticOnNhd ℂ g (ball ρ R))
    (hiso : ∀ z ∈ ball ρ R, z ≠ ρ → g z ≠ 0)
    {m : ℕ} (hm : analyticOrderAt g ρ = m) :
    ∃ u : ℂ → ℂ, AnalyticOnNhd ℂ u (ball ρ R) ∧ (∀ z ∈ ball ρ R, u z ≠ 0) ∧
      ∀ z ∈ chartRA ρ r₀ R ∪ chartLA ρ r₀ R,
        ‖g z - (((List.replicate m ρ).map (fun w => z - w)).prod) * u z‖
          < ‖(((List.replicate m ρ).map (fun w => z - w)).prod) * u z‖ := by
  refine exists_dominating_split_of_configuration (le_of_lt h0) hrR
    (le_refl 0) h0 hg hiso hm (List.replicate m ρ) ?_
    (by simp) ?_
  · intro w hw
    obtain ⟨-, rfl⟩ := List.mem_replicate.mp hw
    simp
  · rw [show (m : ℝ) * 0 * (R + 0) ^ (m - 1) = 0 by ring, sub_zero]
    exact pow_pos h0 m

/-! ### §7 The constraint system, settled -/

/-- **The constraint system on one pinned annulus**: a hole-confined placement
with the smallness margin is the zero list of SOME member dominating ξ on the
charts of an isolating annulus IF AND ONLY IF its count is the central ξ-order.
Compatible configurations are exactly the count-`m` ones: the positions inside
the hole are completely free, and only the count is pinned — the finite
carrier's hole-zero disposition carries no information beyond the count. -/
theorem xi_dominating_configuration_iff {ρ : ℂ} {r₀ r₁ R : ℝ}
    (h0 : 0 < r₀) (hrR : r₀ < R) (hr₁0 : 0 ≤ r₁) (hr₁ : r₁ < r₀)
    (hiso : ∀ z ∈ ball ρ R, z ≠ ρ → xi z ≠ 0)
    {m : ℕ} (hm : analyticOrderAt xi ρ = m)
    (hsmall : (m : ℝ) * r₁ * (R + r₁) ^ (m - 1) < (r₀ - r₁) ^ m)
    (zs : List ℂ) (hzs : ∀ w ∈ zs, ‖w - ρ‖ ≤ r₁) :
    (∃ F u : ℂ → ℂ, AnalyticOnNhd ℂ u (ball ρ R) ∧
      (∀ z ∈ ball ρ R, u z ≠ 0) ∧
      (∀ z ∈ chartRA ρ r₀ R ∪ chartLA ρ r₀ R,
        F z = ((zs.map (fun w => z - w)).prod) * u z) ∧
      (∀ z ∈ chartRA ρ r₀ R ∪ chartLA ρ r₀ R, ‖xi z - F z‖ < ‖F z‖))
    ↔ zs.length = m := by
  constructor
  · rintro ⟨F, u, huan, hune, hfactF, hdom⟩
    have hc := enclosed_count_eq_of_split_domination (le_of_lt h0) hrR hiso
      huan hune (fun w hw => le_trans (hzs w hw) (le_of_lt hr₁)) hfactF hdom
    rw [hm, ENat.toNat_coe] at hc
    exact hc.symm
  · intro hlen
    obtain ⟨u, huan, hune, hdom⟩ := exists_dominating_split_of_configuration
      (le_of_lt h0) hrR hr₁0 hr₁ (xi_analyticOnNhd _) hiso hm zs hzs hlen
      hsmall
    exact ⟨fun z => ((zs.map (fun w => z - w)).prod) * u z, u, huan, hune,
      fun z _ => rfl, hdom⟩

/-! ### §8 Indexed constraint surface -/

/-- A positive-multiplicity indexed centre appears in its repeated configuration
list. -/
theorem configList_mem_center {ι : Type*} {s : Finset ι} {ρc : ι → ℂ}
    {m : ι → ℕ} {i : ι} (hi : i ∈ s) (hmi : 0 < m i) :
    ρc i ∈ configList s ρc m := by
  rw [configList, List.mem_flatMap]
  exact ⟨i, Finset.mem_toList.mpr hi,
    List.mem_replicate.mpr ⟨ne_of_gt hmi, rfl⟩⟩

/-- **Indexed open-hole confinement**: if an indexed split-form member dominates
ξ on the slit-annulus charts, then every positive-multiplicity centre is
strictly inside the hole. -/
theorem indexed_dominating_split_zeros_lt_hole {ι : Type*} (s : Finset ι)
    (ρc : ι → ℂ) (mult : ι → ℕ) {ρ : ℂ} {r₀ R : ℝ}
    (h0 : 0 < r₀) (hrR : r₀ < R)
    (hiso : ∀ z ∈ ball ρ R, z ≠ ρ → xi z ≠ 0)
    {u : ℂ → ℂ}
    (hu_an : AnalyticOnNhd ℂ u (ball ρ R))
    (hρc : ∀ i ∈ s, ‖ρc i - ρ‖ ≤ r₀)
    (hdom : ∀ z ∈ chartRA ρ r₀ R ∪ chartLA ρ r₀ R,
      ‖xi z - (∏ i ∈ s, (z - ρc i) ^ mult i) * u z‖
        < ‖(∏ i ∈ s, (z - ρc i) ^ mult i) * u z‖) :
    ∀ i ∈ s, 0 < mult i → ‖ρc i - ρ‖ < r₀ := by
  have hlist : ∀ w ∈ configList s ρc mult, ‖w - ρ‖ < r₀ := by
    refine dominating_split_zeros_lt_hole h0 hrR hiso hu_an
      (configList_mem hρc) ?_
    intro z hz
    simpa [configList_map_prod] using hdom z hz
  intro i hi hmi
  exact hlist (ρc i) (configList_mem_center hi hmi)

/-- **The indexed constraint system on one pinned annulus**: a hole-confined
indexed placement with the smallness margin is the zero configuration of some
member dominating ξ on the charts if and only if its total multiplicity is the
central ξ-order. -/
theorem xi_dominating_indexed_configuration_iff {ι : Type*} (s : Finset ι)
    (ρc : ι → ℂ) (mult : ι → ℕ) {ρ : ℂ} {r₀ r₁ R : ℝ}
    (h0 : 0 < r₀) (hrR : r₀ < R) (hr₁0 : 0 ≤ r₁) (hr₁ : r₁ < r₀)
    (hiso : ∀ z ∈ ball ρ R, z ≠ ρ → xi z ≠ 0)
    {m : ℕ} (hm : analyticOrderAt xi ρ = m)
    (hsmall : (m : ℝ) * r₁ * (R + r₁) ^ (m - 1) < (r₀ - r₁) ^ m)
    (hρc : ∀ i ∈ s, ‖ρc i - ρ‖ ≤ r₁) :
    (∃ F u : ℂ → ℂ, AnalyticOnNhd ℂ u (ball ρ R) ∧
      (∀ z ∈ ball ρ R, u z ≠ 0) ∧
      (∀ z ∈ chartRA ρ r₀ R ∪ chartLA ρ r₀ R,
        F z = (∏ i ∈ s, (z - ρc i) ^ mult i) * u z) ∧
      (∀ z ∈ chartRA ρ r₀ R ∪ chartLA ρ r₀ R, ‖xi z - F z‖ < ‖F z‖))
    ↔ ∑ i ∈ s, mult i = m := by
  have hiff := xi_dominating_configuration_iff (ρ := ρ) (r₀ := r₀) (r₁ := r₁)
    (R := R) h0 hrR hr₁0 hr₁ hiso hm hsmall
    (configList s ρc mult) (configList_mem hρc)
  simpa [configList_map_prod, configList_length] using hiff

end RHTower
