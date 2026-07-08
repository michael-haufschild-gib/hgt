/-
Splitting a dominating member on the annulus: cover, finiteness, complete peeling, and
the parity certificate in boundary form.

The two slit charts cover the full annulus, so a member dominating ξ on the charts is
nonvanishing on the whole annulus and its ball zeros are confined to the hole.  An
analytic member with a nonvanishing point has finitely many zeros in the closed hole (an
accumulation point would force it to vanish identically on the ball), and a finite
hole-confined zero set peels off completely: iterating the single-zero peel produces the
SPLIT — a list of hole centres, one per zero counted with multiplicity, and a cofactor
nonvanishing on the whole ball.  The split clause of the carrier weld is therefore a
theorem, and the anchored event ledger follows from domination plus one parity.

That parity is a boundary object: any analytic square roots of a split member on the two
slit charts have deck class `exp(2πi·count/2)`, so the count is even exactly when the
member's own mod-2 deck cocycle is trivial — a carrier-side datum with no reference
to ξ.
-/
import GaloisForLFunctions.RHTower.CarrierWeld

namespace RHTower

open Complex Metric

/-! ### The slit charts cover the annulus -/

/-- The union of the two slit annulus charts is the whole annulus: away from the centre
every point avoids one of the two slits. -/
theorem charts_union_eq_annulus (a : ℂ) {r₀ R : ℝ} (h0 : 0 ≤ r₀) :
    chartRA a r₀ R ∪ chartLA a r₀ R = ball a R \ closedBall a r₀ :=
  Set.Subset.antisymm
    (Set.union_subset (fun _ hz => hz.2) (fun _ hz => hz.2))
    (annulus_subset_charts h0)

/-! ### Finiteness of the hole zeros -/

/-- An analytic member with a nonvanishing point has finitely many zeros in the closed
hole: an infinite zero set in the compact hole would accumulate, and at an accumulation
point the isolated-zeros alternative forces the member to vanish identically on the
ball. -/
theorem finite_closedBall_zeros {F : ℂ → ℂ} {ρ : ℂ} {r₀ R : ℝ} (hrR : r₀ < R)
    (hFan : AnalyticOnNhd ℂ F (ball ρ R))
    (hne : ∃ z ∈ ball ρ R, F z ≠ 0) :
    {z | z ∈ closedBall ρ r₀ ∧ F z = 0}.Finite := by
  by_contra hfin'
  have hinf : Set.Infinite {z | z ∈ closedBall ρ r₀ ∧ F z = 0} := hfin'
  set g := hinf.natEmbedding with hg_def
  set seq : ℕ → ℂ := fun n => (g n).1 with hseq_def
  have hmem : ∀ n : ℕ, seq n ∈ closedBall ρ r₀ := fun n => (g n).2.1
  obtain ⟨x, hx, φ, hφ, hlim⟩ := (isCompact_closedBall ρ r₀).tendsto_subseq hmem
  have hxball : x ∈ ball ρ R := Metric.closedBall_subset_ball hrR hx
  rcases (hFan x hxball).eventually_eq_zero_or_eventually_ne_zero with hz | hnz
  · have hev : F =ᶠ[nhds x] 0 := by
      filter_upwards [hz] with w hw
      simpa using hw
    have heq := hFan.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball ρ R).isPreconnected hxball hev
    obtain ⟨z, hzball, hzne⟩ := hne
    exact hzne (heq hzball)
  · rw [eventually_nhdsWithin_iff] at hnz
    have hlim' := hlim.eventually hnz
    have hevx : ∀ᶠ n in Filter.atTop, seq (φ n) = x := by
      filter_upwards [hlim'] with n hn
      by_contra hne'
      exact hn (by simpa using hne') ((g (φ n)).2.2)
    rw [Filter.eventually_atTop] at hevx
    obtain ⟨n₀, hn₀⟩ := hevx
    have h1 : seq (φ n₀) = x := hn₀ n₀ le_rfl
    have h2 : seq (φ (n₀ + 1)) = x := hn₀ (n₀ + 1) (by omega)
    have h3 : g (φ n₀) = g (φ (n₀ + 1)) := Subtype.ext (h1.trans h2.symm)
    have h4 := hφ.injective (g.injective h3)
    omega

/-! ### Complete peeling of a finite hole-confined zero set -/

/-- Iterated single-zero peeling: an analytic member whose ball zeros form a finite set
confined to the hole splits completely into hole-centred linear factors, one per zero
counted with multiplicity, times a cofactor nonvanishing on the whole ball.  The
recursion peels one zero, notes that the cofactor's zero set is the original minus the
peeled point (the peel preserves orders away from its centre), and descends on the
cardinality. -/
theorem exists_split_of_finite_zeros_aux {ρ : ℂ} {r₀ R : ℝ} :
    ∀ (n : ℕ) (F : ℂ → ℂ),
      AnalyticOnNhd ℂ F (ball ρ R) →
      (∃ z ∈ ball ρ R, F z ≠ 0) →
      (∀ z ∈ ball ρ R, F z = 0 → ‖z - ρ‖ ≤ r₀) →
      ∀ (hfin : {z | z ∈ ball ρ R ∧ F z = 0}.Finite), hfin.toFinset.card = n →
      ∃ (zs : List ℂ) (u : ℂ → ℂ),
        (∀ w ∈ zs, ‖w - ρ‖ ≤ r₀) ∧
        AnalyticOnNhd ℂ u (ball ρ R) ∧ (∀ z ∈ ball ρ R, u z ≠ 0) ∧
        ∀ z ∈ ball ρ R, F z = ((zs.map (fun w => z - w)).prod) * u z := by
  intro n
  induction n with
  | zero =>
      intro F hFan hne hsub hfin hcard
      refine ⟨[], F, by simp, hFan, ?_, by simp⟩
      intro z hz
      by_contra h0
      have hmem : z ∈ hfin.toFinset := hfin.mem_toFinset.mpr ⟨hz, h0⟩
      rw [Finset.card_eq_zero.mp hcard] at hmem
      exact absurd hmem (Finset.notMem_empty z)
  | succ k ih =>
      intro F hFan hne hsub hfin hcard
      have hnonempty : hfin.toFinset.Nonempty := by
        rw [← Finset.card_pos, hcard]
        omega
      obtain ⟨z₀, hz₀mem⟩ := hnonempty
      have hz₀ : z₀ ∈ ball ρ R ∧ F z₀ = 0 := hfin.mem_toFinset.mp hz₀mem
      have hnetop : analyticOrderAt F z₀ ≠ ⊤ := by
        intro htop
        have hev : F =ᶠ[nhds z₀] 0 := by
          filter_upwards [analyticOrderAt_eq_top.mp htop] with w hw
          simpa using hw
        have heq := hFan.eqOn_zero_of_preconnected_of_eventuallyEq_zero
          (convex_ball ρ R).isPreconnected hz₀.1 hev
        obtain ⟨z, hzball, hzne⟩ := hne
        exact hzne (heq hzball)
      have hm : analyticOrderAt F z₀ = ((analyticOrderAt F z₀).toNat : ℕ∞) :=
        (ENat.coe_toNat hnetop).symm
      obtain ⟨h, hhan, hh0, hfact, horders⟩ := exists_peel isOpen_ball hFan hz₀.1 hm
      have hzset : {z | z ∈ ball ρ R ∧ h z = 0} =
          {z | z ∈ ball ρ R ∧ F z = 0} \ {z₀} := by
        ext w
        simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hwball, hw0⟩
          have hwne : w ≠ z₀ := by
            intro he
            rw [he] at hw0
            exact hh0 hw0
          refine ⟨⟨hwball, ?_⟩, hwne⟩
          by_contra hFne
          have hzero : analyticOrderAt F w = 0 :=
            analyticOrderAt_eq_zero.mpr (Or.inr hFne)
          rw [← horders w hwball hwne] at hzero
          rcases analyticOrderAt_eq_zero.mp hzero with hna | hne'
          · exact hna (hhan w hwball)
          · exact hne' hw0
        · rintro ⟨⟨hwball, hw0⟩, hwne⟩
          refine ⟨hwball, ?_⟩
          by_contra hhne
          have hzero : analyticOrderAt h w = 0 :=
            analyticOrderAt_eq_zero.mpr (Or.inr hhne)
          rw [horders w hwball hwne] at hzero
          rcases analyticOrderAt_eq_zero.mp hzero with hna | hne'
          · exact hna (hFan w hwball)
          · exact hne' hw0
      have hfin' : {z | z ∈ ball ρ R ∧ h z = 0}.Finite := by
        rw [hzset]
        exact hfin.diff
      have hcard' : hfin'.toFinset.card = k := by
        have htf : hfin'.toFinset = hfin.toFinset.erase z₀ := by
          ext w
          simp only [Set.Finite.mem_toFinset, Finset.mem_erase, hzset, Set.mem_diff,
            Set.mem_singleton_iff]
          tauto
        rw [htf, Finset.card_erase_of_mem hz₀mem, hcard]
        omega
      have hne' : ∃ z ∈ ball ρ R, h z ≠ 0 := ⟨z₀, hz₀.1, hh0⟩
      have hsub' : ∀ z ∈ ball ρ R, h z = 0 → ‖z - ρ‖ ≤ r₀ := by
        intro z hz hz0
        have hmem : z ∈ {z | z ∈ ball ρ R ∧ h z = 0} := ⟨hz, hz0⟩
        rw [hzset] at hmem
        exact hsub z hz hmem.1.2
      obtain ⟨zs', u, hzs', huan, hune, hufact⟩ := ih h hhan hne' hsub' hfin' hcard'
      refine ⟨List.replicate (analyticOrderAt F z₀).toNat z₀ ++ zs', u, ?_, huan, hune,
        ?_⟩
      · intro w hw
        rcases List.mem_append.mp hw with hw | hw
        · rw [List.eq_of_mem_replicate hw]
          exact hsub z₀ hz₀.1 hz₀.2
        · exact hzs' w hw
      · intro z hz
        rw [List.map_append, List.prod_append, List.map_replicate, List.prod_replicate,
          hfact z hz, hufact z hz]
        ring

/-- **Complete peeling.**  An analytic member with a nonvanishing point whose ball zeros
are confined to the hole splits into hole-centred linear factors times a
ball-nonvanishing cofactor. -/
theorem exists_split_of_finite_zeros {ρ : ℂ} {r₀ R : ℝ} {F : ℂ → ℂ}
    (hFan : AnalyticOnNhd ℂ F (ball ρ R))
    (hne : ∃ z ∈ ball ρ R, F z ≠ 0)
    (hsub : ∀ z ∈ ball ρ R, F z = 0 → ‖z - ρ‖ ≤ r₀)
    (hfin : {z | z ∈ ball ρ R ∧ F z = 0}.Finite) :
    ∃ (zs : List ℂ) (u : ℂ → ℂ),
      (∀ w ∈ zs, ‖w - ρ‖ ≤ r₀) ∧
      AnalyticOnNhd ℂ u (ball ρ R) ∧ (∀ z ∈ ball ρ R, u z ≠ 0) ∧
      ∀ z ∈ ball ρ R, F z = ((zs.map (fun w => z - w)).prod) * u z :=
  exists_split_of_finite_zeros_aux hfin.toFinset.card F hFan hne hsub hfin rfl

/-! ### The split clause of the weld is a theorem -/

/-- **Domination splits.**  A member analytic near the ball that dominates ξ on the slit
charts is nonvanishing on the whole annulus (the charts cover it), its zeros are confined
to the hole and finite, and complete peeling yields the split. -/
theorem exists_split_of_domination {ρ : ℂ} {r₀ R : ℝ} (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    {F : ℂ → ℂ} (hFan : AnalyticOnNhd ℂ F (ball ρ R))
    (hdom : ∀ z ∈ chartRA ρ r₀ R ∪ chartLA ρ r₀ R, ‖xi z - F z‖ < ‖F z‖) :
    ∃ (zs : List ℂ) (u : ℂ → ℂ),
      (∀ w ∈ zs, ‖w - ρ‖ ≤ r₀) ∧
      AnalyticOnNhd ℂ u (ball ρ R) ∧ (∀ z ∈ ball ρ R, u z ≠ 0) ∧
      ∀ z ∈ ball ρ R, F z = ((zs.map (fun w => z - w)).prod) * u z := by
  have hFne : ∀ z ∈ ball ρ R \ closedBall ρ r₀, F z ≠ 0 := by
    intro z hz h0'
    have hzc : z ∈ chartRA ρ r₀ R ∪ chartLA ρ r₀ R := by
      rw [charts_union_eq_annulus ρ h0]
      exact hz
    have hlt := hdom z hzc
    rw [h0', sub_zero, norm_zero] at hlt
    exact absurd hlt (not_lt.mpr (norm_nonneg _))
  have hne : ∃ z ∈ ball ρ R, F z ≠ 0 := by
    have hPmem := (annulus_basepoints_mem (a := ρ) h0 hrR).1.1
    exact ⟨ρ + (((r₀ + R) / 2 : ℝ) : ℂ) * I, hPmem.2.1, hFne _ hPmem.2⟩
  have hsub : ∀ z ∈ ball ρ R, F z = 0 → ‖z - ρ‖ ≤ r₀ := by
    intro z hz h0'
    by_contra hgt
    refine hFne z ⟨hz, fun hc => hgt ?_⟩ h0'
    rw [mem_closedBall, dist_eq_norm] at hc
    exact hc
  have hfin : {z | z ∈ ball ρ R ∧ F z = 0}.Finite := by
    refine Set.Finite.subset (finite_closedBall_zeros hrR hFan hne) ?_
    intro z hz
    exact ⟨mem_closedBall.mpr (by rw [dist_eq_norm]; exact hsub z hz.1 hz.2), hz.2⟩
  exact exists_split_of_finite_zeros hFan hne hsub hfin

/-! ### The weld from domination and one parity -/

/-- **The anchored event ledger from domination and a parity certificate.**  The split
clause is discharged: a member analytic near the ball, dominating ξ on the slit charts,
all of whose splits have even count, yields the anchored event ledger for ξ. -/
theorem anchoredEventLedger_of_domination {ρ : ℂ} {r₀ R : ℝ} (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    {F : ℂ → ℂ} (hFan : AnalyticOnNhd ℂ F (ball ρ R))
    (hdom : ∀ z ∈ chartRA ρ r₀ R ∪ chartLA ρ r₀ R, ‖xi z - F z‖ < ‖F z‖)
    (hpar : ∀ (zs : List ℂ) (u : ℂ → ℂ),
      (∀ w ∈ zs, ‖w - ρ‖ ≤ r₀) →
      AnalyticOnNhd ℂ u (ball ρ R) → (∀ z ∈ ball ρ R, u z ≠ 0) →
      (∀ z ∈ ball ρ R, F z = ((zs.map (fun w => z - w)).prod) * u z) →
      Even zs.length) :
    AnchoredEventLedger ρ r₀ R xi := by
  obtain ⟨zs, u, hzs, huan, hune, hufact⟩ := exists_split_of_domination h0 hrR hFan hdom
  have hchartsub : ∀ z ∈ chartRA ρ r₀ R ∪ chartLA ρ r₀ R, z ∈ ball ρ R := by
    intro z hz
    rw [charts_union_eq_annulus ρ h0] at hz
    exact hz.1
  exact anchoredEventLedger_of_carrier_domination huan hune hzs
    (fun z hz => hufact z (hchartsub z hz)) hdom (hpar zs u hzs huan hune hufact)

/-- **The base rung from domination and parity.**  If every hypothetical off-line ξ-zero
admits an isolating annulus and a member analytic near the ball that dominates ξ on the
slit charts and all of whose splits have even count, then every off-line vanishing order
is even.  The split clause of the supply is gone; what remains is the domination and the
parity. -/
theorem rhLadder_one_of_domination_parity
    (hsupply : ∀ ρ ∈ rightHalf, xi ρ = 0 → ∃ (r₀ R : ℝ) (F : ℂ → ℂ),
      0 ≤ r₀ ∧ r₀ < R ∧ (∀ z ∈ ball ρ R, z ≠ ρ → xi z ≠ 0) ∧
      AnalyticOnNhd ℂ F (ball ρ R) ∧
      (∀ z ∈ chartRA ρ r₀ R ∪ chartLA ρ r₀ R, ‖xi z - F z‖ < ‖F z‖) ∧
      (∀ (zs : List ℂ) (u : ℂ → ℂ),
        (∀ w ∈ zs, ‖w - ρ‖ ≤ r₀) →
        AnalyticOnNhd ℂ u (ball ρ R) → (∀ z ∈ ball ρ R, u z ≠ 0) →
        (∀ z ∈ ball ρ R, F z = ((zs.map (fun w => z - w)).prod) * u z) →
        Even zs.length)) :
    RHLadder 1 := by
  refine rhLadder_one_of_isolating_anchoredEventLedgers ?_
  intro ρ hρ h0
  obtain ⟨r₀, R, F, h1, h2, hiso, hFan, hdom, hpar⟩ := hsupply ρ hρ h0
  exact ⟨r₀, R, h1, h2, hiso, anchoredEventLedger_of_domination h1 h2 hFan hdom hpar⟩

/-! ### The parity certificate in boundary form -/

/-- The list product over the split centres as a `Fin`-indexed product. -/
theorem list_prod_map_eq_fin_prod (zs : List ℂ) (z : ℂ) :
    ((zs.map (fun w => z - w)).prod) = ∏ i : Fin zs.length, (z - zs.get i) := by
  conv_lhs => rw [← List.ofFn_get zs]
  rw [List.map_ofFn, List.prod_ofFn]
  rfl

/-- **The parity is the member's own mod-2 deck cocycle.**  Any analytic square roots of
a split member on the two slit charts have deck class `exp(2πi·count/2)`: the class is
trivial exactly when the count is even.  The parity the weld consumes is a carrier-side
boundary datum. -/
theorem split_deckClass_one_iff_even {ρ : ℂ} {r₀ R : ℝ} (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    {F u : ℂ → ℂ} {zs : List ℂ}
    (hzs : ∀ w ∈ zs, ‖w - ρ‖ ≤ r₀)
    (huan : AnalyticOnNhd ℂ u (ball ρ R)) (hune : ∀ z ∈ ball ρ R, u z ≠ 0)
    (hufact : ∀ z ∈ ball ρ R, F z = ((zs.map (fun w => z - w)).prod) * u z)
    {G₁ G₂ : ℂ → ℂ}
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartRA ρ r₀ R))
    (hG₂ : AnalyticOnNhd ℂ G₂ (chartLA ρ r₀ R))
    (hpG₁ : ∀ z ∈ chartRA ρ r₀ R, G₁ z ^ 2 = F z)
    (hpG₂ : ∀ z ∈ chartLA ρ r₀ R, G₂ z ^ 2 = F z) :
    deckClass G₁ G₂ (ρ + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
        (ρ - (((r₀ + R) / 2 : ℝ) : ℂ) * I) = 1 ↔ Even zs.length := by
  have hmz := deckClass_multi_zero (Finset.univ : Finset (Fin zs.length))
    (fun i => zs.get i) (fun _ => 1) h0 hrR (by norm_num : (0 : ℕ) < 2)
    (fun i _ => hzs (zs.get i) (List.get_mem zs i))
    huan hune
    (fun z hz => by
      simp only [pow_one]
      rw [hufact z hz, list_prod_map_eq_fin_prod])
    hG₁ hG₂ hpG₁ hpG₂
  have hsum : (∑ _i : Fin zs.length, ((1 : ℕ) : ℂ)) = (zs.length : ℂ) := by
    simp
  rw [hsum] at hmz
  rw [hmz, exp_two_pi_mul_div_eq_one_iff (by norm_num : (0 : ℕ) < 2) zs.length]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, by omega⟩
  · intro h
    exact h.two_dvd

end RHTower
