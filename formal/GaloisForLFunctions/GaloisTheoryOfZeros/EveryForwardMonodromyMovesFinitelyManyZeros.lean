import GaloisForLFunctions.GaloisTheoryOfZeros.TheTransportOfAZeroDependsOnlyOnTheHomotopyClass
import GaloisForLFunctions.GaloisTheoryOfZeros.ConjugationOfTheZerosIsAMonodromyOfTheHeatCover
import GaloisForLFunctions.RHTower.LocalRectangleArgumentBound

/-!
# Every forward monodromy moves finitely many zeros

A loop of forward times lies in a box `{t₀ ≤ Re τ, ‖τ‖ ≤ T₀}`, and so does its straight
contraction to the base point. Over the box the far zeros are simple, and a zero that starts far
out moves by at most `1/2` while the time moves by at most `1/12`.

* **The trap along a whole path** (`exists_forall_norm_sub_le_of_long_zero_path`). If the path
  of times moves by at most `1/12` on every parameter interval of length `1/N`, a continuous
  family of zeros that starts at modulus `≥ R + N/2` moves by at most `N/2`.
* **Far zeros return** (`exists_forall_transports_self_of_far`). A zero of large modulus lifts
  along every loop of the contraction, through simple zeros, although the contraction crosses
  branch times. By homotopy invariance the loop transports the zero to itself.
* **Finite support** (`finite_setOf_forwardMonodromy_ne`). Every element of the forward
  monodromy group moves finitely many zeros: the group consists of restricted signed
  permutations of the pairs `{z, −z}`.
* **The reflection is not a forward monodromy** (`fibreNeg_not_mem_forwardMonodromy`). Every
  fibre over a forward time off the branch times is infinite (`infinite_fibre`), and `z ↦ −z`
  moves every zero except `0`. So the reflection of the functional equation commutes with the
  group and is not in it, whereas conjugation over a real time is an element.
-/

open Complex Filter Topology Set Metric
open RHTower RHTower.DeBruijn

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

/-! ## The trap along a whole path -/

/-- A path of times on `[0, 1]` moves by at most `1/12` on parameter intervals of length `1/N`,
for some `N`. -/
theorem exists_nat_forall_norm_sub_le {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc 0 1)) :
    ∃ N : ℕ, 0 < N ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1, |s - s'| ≤ 1 / N →
      ‖γ s - γ s'‖ ≤ 1 / 12 := by
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hγ
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff_le.1 huc (1 / 12) (by norm_num)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  refine ⟨n + 1, Nat.succ_pos n, fun s hs s' hs' hd => ?_⟩
  rw [← dist_eq_norm]
  refine hmod s hs s' hs' ?_
  rw [Real.dist_eq]
  push_cast at hd
  exact hd.trans hn.le

/-- **The trap along a whole path.** Over a box of forward times, let the path of times move by
at most `1/12` on every parameter interval of length `1/N`. A continuous family of zeros along
the path that starts at modulus `≥ R + N/2` moves by at most `N/2`. -/
theorem exists_forall_norm_sub_le_of_long_zero_path {t₀ : ℝ} (T₀ : ℝ) (ht₀ : 0 < t₀) :
    ∃ R : ℝ, ∀ (δ w : ℝ → ℂ) (N : ℕ) (b : ℝ), 0 < N → b ≤ 1 → ContinuousOn δ (Icc 0 b) →
      ContinuousOn w (Icc 0 b) →
      (∀ s ∈ Icc (0 : ℝ) b, t₀ ≤ (δ s).re ∧ ‖δ s‖ ≤ T₀ ∧ complexHeat (δ s) (w s) = 0) →
      (∀ s ∈ Icc (0 : ℝ) b, ∀ s' ∈ Icc (0 : ℝ) b, |s - s'| ≤ 1 / N →
        ‖δ s - δ s'‖ ≤ 1 / 12) →
      R + N / 2 ≤ ‖w 0‖ → ∀ s ∈ Icc (0 : ℝ) b, ‖w s - w 0‖ ≤ N / 2 := by
  obtain ⟨R, hR⟩ := exists_forall_norm_sub_le_of_zero_path T₀ ht₀
  refine ⟨R, fun δ w N b hN hb hδ hw hbox hmod hfar => ?_⟩
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 hN
  -- up to the parameter `k/N` the zero has moved by at most `k/2`
  have key : ∀ k : ℕ, ∀ s ∈ Icc (0 : ℝ) b, s ≤ k / N → ‖w s - w 0‖ ≤ k / 2 := by
    intro k
    induction k with
    | zero =>
      intro s hs hsk
      have hs0 : s = 0 := le_antisymm (by simpa using hsk) hs.1
      rw [hs0, sub_self, norm_zero]
      simp
    | succ k ih =>
      intro s hs hsk
      rcases le_or_gt s (k / N) with h | h
      · refine (ih s hs h).trans ?_
        push_cast
        linarith
      · have hs₁ : (k : ℝ) / N ∈ Icc (0 : ℝ) b := ⟨by positivity, h.le.trans hs.2⟩
        have hkN : (k : ℝ) < N := by
          have h1 : (k : ℝ) / N < 1 := h.trans_le (hs.2.trans hb)
          rwa [div_lt_one hNpos] at h1
        have h1 := ih _ hs₁ le_rfl
        have hfar₁ : R ≤ ‖w (k / N)‖ := by
          have h2 := norm_sub_norm_le (w 0) (w (k / N))
          rw [norm_sub_rev] at h2
          linarith
        have hsub : Icc ((k : ℝ) / N) s ⊆ Icc 0 b := Icc_subset_Icc hs₁.1 hs.2
        have h2 := hR δ w (k / N) s (hδ.mono hsub) (hw.mono hsub) (fun s' hs' => by
          obtain ⟨h3, h4, h5⟩ := hbox s' (hsub hs')
          refine ⟨h3, h4, hmod s' (hsub hs') _ hs₁ ?_, h5⟩
          rw [abs_of_nonneg (sub_nonneg.2 hs'.1)]
          have h6 : s' ≤ ((k + 1 : ℕ) : ℝ) / N := hs'.2.trans hsk
          push_cast at h6
          rw [add_div] at h6
          linarith) hfar₁ s ⟨h.le, le_rfl⟩
        calc ‖w s - w 0‖ ≤ ‖w s - w (k / N)‖ + ‖w (k / N) - w 0‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ 1 / 2 + k / 2 := add_le_add h2 h1
          _ = ((k + 1 : ℕ) : ℝ) / 2 := by push_cast; ring
  intro s hs
  exact key N s hs (by rw [div_self hNpos.ne']; exact hs.2.trans hb)

/-! ## Far zeros return -/

/-- **Far zeros return.** Let a loop of times lie in a box of forward times and move by at most
`1/12` on parameter intervals of length `1/N`. Then it transports every zero of modulus `≥ R`
to itself; `R` depends on the box and on `N` only. The loop may be homotopic to a constant only
across branch times. -/
theorem exists_forall_transports_self_of_far {t₀ : ℝ} (T₀ : ℝ) (ht₀ : 0 < t₀) {N : ℕ}
    (hN : 0 < N) :
    ∃ R : ℝ, ∀ γ : ℝ → ℂ, ContinuousOn γ (Icc 0 1) → γ 1 = γ 0 →
      (∀ s ∈ Icc (0 : ℝ) 1, t₀ ≤ (γ s).re ∧ ‖γ s‖ ≤ T₀) →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1, |s - s'| ≤ 1 / N →
        ‖γ s - γ s'‖ ≤ 1 / 12) →
      ∀ z₀ : ℂ, complexHeat (γ 0) z₀ = 0 → R ≤ ‖z₀‖ → Transports γ z₀ z₀ := by
  obtain ⟨R₁, hR₁⟩ := exists_forall_norm_sub_le_of_long_zero_path T₀ ht₀
  obtain ⟨R₂, hR₂⟩ := exists_deriv_complexHeat_ne_zero T₀ ht₀
  refine ⟨max R₁ R₂ + N / 2, fun γ hγ hloop hbox hmod z₀ hz₀ hfar => ?_⟩
  have h00 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  -- the contraction stays in the box, which is convex
  have hboxc : ∀ u ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      t₀ ≤ (contractPath γ (γ 0) u s).re ∧ ‖contractPath γ (γ 0) u s‖ ≤ T₀ := by
    intro u hu s hs
    obtain ⟨h1, h2⟩ := hbox s hs
    obtain ⟨h3, h4⟩ := hbox 0 h00
    constructor
    · rw [contractPath, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
      exact le_convexCombo hu.1 hu.2 h1 h3
    · calc ‖contractPath γ (γ 0) u s‖ ≤ ‖((1 - u : ℝ) : ℂ) * γ s‖ + ‖(u : ℂ) * γ 0‖ :=
            norm_add_le _ _
        _ = (1 - u) * ‖γ s‖ + u * ‖γ 0‖ := by
            rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
              Real.norm_of_nonneg (sub_nonneg.2 hu.2), Real.norm_of_nonneg hu.1]
        _ ≤ T₀ := convexCombo_le hu.1 hu.2 h2 h4
  -- and it moves no faster than the loop
  have hmodc : ∀ u ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1,
      |s - s'| ≤ 1 / N → ‖contractPath γ (γ 0) u s - contractPath γ (γ 0) u s'‖ ≤ 1 / 12 := by
    intro u hu s hs s' hs' hd
    have h1 : contractPath γ (γ 0) u s - contractPath γ (γ 0) u s' =
        ((1 - u : ℝ) : ℂ) * (γ s - γ s') := by
      simp only [contractPath]
      ring
    rw [h1, norm_mul, Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.2 hu.2)]
    calc (1 - u) * ‖γ s - γ s'‖ ≤ 1 * ‖γ s - γ s'‖ :=
          mul_le_mul_of_nonneg_right (by linarith [hu.1]) (norm_nonneg _)
      _ ≤ 1 / 12 := by rw [one_mul]; exact hmod s hs s' hs' hd
  refine transports_self_of_contraction hγ hloop fun u hu => ?_
  have hδc := continuousOn_contractPath_right hγ (γ 0) hu
  -- a lift of a far zero stays in the region where the zeros are simple
  have hstay : ∀ b ∈ Icc (0 : ℝ) 1, ∀ z, IsZeroLift (contractPath γ (γ 0) u) b z → z 0 = z₀ →
      ∀ s ∈ Icc (0 : ℝ) b, z s ∈ {z : ℂ | max R₁ R₂ ≤ ‖z‖} := by
    intro b hb z hz hz0 s hs
    have hsub : Icc (0 : ℝ) b ⊆ Icc 0 1 := Icc_subset_Icc_right hb.2
    have h := hR₁ (contractPath γ (γ 0) u) z N b hN hb.2 (hδc.mono hsub) hz.continuousOn
      (fun s' hs' => ⟨(hboxc u hu s' (hsub hs')).1, (hboxc u hu s' (hsub hs')).2,
        hz.zero s' hs'⟩)
      (fun s' hs' s'' hs'' hd => hmodc u hu s' (hsub hs') s'' (hsub hs'') hd)
      (by rw [hz0]; linarith [le_max_left R₁ R₂]) s hs
    have h2 := norm_sub_norm_le (z 0) (z s)
    rw [norm_sub_rev, hz0] at h2
    show max R₁ R₂ ≤ ‖z s‖
    linarith
  have hK : IsClosed {z : ℂ | max R₁ R₂ ≤ ‖z‖} := isClosed_le continuous_const continuous_norm
  have hsimple : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z ∈ {z : ℂ | max R₁ R₂ ≤ ‖z‖},
      complexHeat (contractPath γ (γ 0) u s) z = 0 →
        deriv (complexHeat (contractPath γ (γ 0) u s)) z ≠ 0 := fun s hs z hz h0 =>
    hR₂ _ z (hboxc u hu s hs).1 (hboxc u hu s hs).2 ((le_max_right R₁ R₂).trans hz) h0
  have h0' : complexHeat (contractPath γ (γ 0) u 0) z₀ = 0 := by
    rw [contractPath_of_eq rfl]
    exact hz₀
  rcases exists_isZeroLift_or_escape_of_mem hδc hK hsimple hstay h0' with ⟨w, hw, hw0⟩ | hesc
  · exact ⟨w, hw, hw0, fun s hs => hsimple s hs (w s)
      (hstay 1 ⟨zero_le_one, le_rfl⟩ w hw hw0 s hs) (hw.zero s hs)⟩
  · exact absurd hesc (not_escapesAlong_of_re_pos hδc
      (fun s hs => ht₀.trans_le (hboxc u hu s hs).1) z₀)

/-! ## Finite support -/

/-- A forward path lies in a box of forward times. -/
theorem IsForwardPath.exists_box {γ : ℝ → ℂ} (hγ : IsForwardPath γ) :
    ∃ t₀ > 0, ∃ T₀ : ℝ, ∀ s ∈ Icc (0 : ℝ) 1, t₀ ≤ (γ s).re ∧ ‖γ s‖ ≤ T₀ := by
  have hne : (Icc (0 : ℝ) 1).Nonempty := nonempty_Icc.2 zero_le_one
  obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn hne
    (Complex.continuous_re.comp_continuousOn hγ.continuousOn)
  obtain ⟨s₁, -, hmax⟩ := isCompact_Icc.exists_isMaxOn hne
    (continuous_norm.comp_continuousOn hγ.continuousOn)
  exact ⟨(γ s₀).re, hγ.re_pos s₀ hs₀, ‖γ s₁‖, fun s hs =>
    ⟨isMinOn_iff.1 hmin s hs, isMaxOn_iff.1 hmax s hs⟩⟩

/-- The zeros of `H_τ` in a closed disc are finite in number. -/
theorem finite_zeros_closedBall (τ : ℂ) (R : ℝ) :
    {z : ℂ | z ∈ closedBall (0 : ℂ) R ∧ complexHeat τ z = 0}.Finite := by
  obtain ⟨x, hx⟩ := exists_complexHeat_ne_zero τ
  exact zeros_closedBall_finite_of_analyticOnNhd (c := 0) (r := R) (R := max R ‖x‖ + 1)
    (by linarith [le_max_left R ‖x‖])
    (fun z _ => (differentiable_complexHeat τ).analyticAt z) (x := x)
    (by rw [mem_ball_zero_iff]; linarith [le_max_right R ‖x‖]) hx

/-- **Every forward monodromy moves finitely many zeros.** The forward monodromy group is a group
of restricted signed permutations of the pairs `{z, −z}`. -/
theorem finite_setOf_forwardMonodromy_ne {τ : ℂ} {hτ : 0 < τ.re} {hb : τ ∉ branchTimes}
    {σ : Equiv.Perm {z : ℂ // complexHeat τ z = 0}} (hσ : σ ∈ forwardMonodromy τ hτ hb) :
    {p | σ p ≠ p}.Finite := by
  obtain ⟨γ, hγ, h0, h1, hT⟩ := hσ
  obtain ⟨t₀, ht₀, T₀, hbox⟩ := hγ.exists_box
  obtain ⟨N, hN, hmod⟩ := exists_nat_forall_norm_sub_le hγ.continuousOn
  obtain ⟨R, hR⟩ := exists_forall_transports_self_of_far T₀ ht₀ hN
  have hfix : ∀ p : {z : ℂ // complexHeat τ z = 0}, R ≤ ‖p.1‖ → σ p = p := fun p hp =>
    Subtype.ext (hγ.transports_unique (hT p)
      (hR γ hγ.continuousOn (h1.trans h0.symm) hbox hmod p.1 (by rw [h0]; exact p.2) hp))
  refine ((finite_zeros_closedBall τ R).preimage Subtype.val_injective.injOn).subset
    fun p hp => ?_
  refine ⟨mem_closedBall_zero_iff.2 ?_, p.2⟩
  by_contra hcon
  exact hp (hfix p (not_le.1 hcon).le)

/-! ## The reflection is not a forward monodromy -/

/-- The fibre of the heat cover over a forward time off the branch times is infinite. -/
theorem infinite_fibre {τ : ℂ} (hτ : 0 < τ.re) (hb : τ ∉ branchTimes) :
    Infinite {z : ℂ // complexHeat τ z = 0} := by
  have h8 : Infinite {z : ℂ // complexHeat ((1 / 8 : ℝ) : ℂ) z = 0} := by
    have hinf := riemannHeat_zeros_infinite (t := 1 / 8) (by norm_num)
    have hset : {z : ℂ | complexHeat ((1 / 8 : ℝ) : ℂ) z = 0} =
        {z : ℂ | riemannHeat (1 / 8) z = 0} := by
      ext z
      simp only [mem_setOf_eq, complexHeat_ofReal]
    rw [← hset] at hinf
    exact Set.infinite_coe_iff.2 hinf
  obtain ⟨γ, hγ, h0, h1⟩ := exists_isForwardPath (τ := ((1 / 8 : ℝ) : ℂ)) (τ' := τ)
    (by rw [Complex.ofReal_re]; norm_num) hτ (ofReal_not_mem_branchTimes_of_eighth_le le_rfl) hb
  obtain ⟨e, -⟩ := hγ.exists_fibreEquiv h0 h1
  exact Infinite.of_injective e e.injective

/-- **The reflection of the functional equation is not a forward monodromy.** The reflection
`z ↦ −z` commutes with the forward monodromy group and does not belong to it: it moves
infinitely many zeros. -/
theorem fibreNeg_not_mem_forwardMonodromy {τ : ℂ} (hτ : 0 < τ.re) (hb : τ ∉ branchTimes) :
    fibreNeg τ ∉ forwardMonodromy τ hτ hb := by
  intro hmem
  have hfin := finite_setOf_forwardMonodromy_ne hmem
  have hinf := infinite_fibre hτ hb
  have hzero : {p : {z : ℂ // complexHeat τ z = 0} | p.1 = 0}.Finite :=
    Set.Subsingleton.finite fun p hp q hq => Subtype.ext ((hp : p.1 = 0).trans (hq : q.1 = 0).symm)
  have huniv : (Set.univ : Set {z : ℂ // complexHeat τ z = 0}).Finite := by
    refine (hfin.union hzero).subset fun p _ => ?_
    by_cases hp : p.1 = 0
    · exact Or.inr hp
    · refine Or.inl fun h => hp ?_
      have h1 : -p.1 = p.1 := congrArg Subtype.val h
      have h2 : (2 : ℂ) * p.1 = 0 := by linear_combination -h1
      exact (mul_eq_zero.1 h2).resolve_left two_ne_zero
  haveI := hinf
  haveI := Set.finite_univ_iff.1 huniv
  exact not_finite {z : ℂ // complexHeat τ z = 0}

end

end GaloisForLFunctions.GaloisTheoryOfZeros
