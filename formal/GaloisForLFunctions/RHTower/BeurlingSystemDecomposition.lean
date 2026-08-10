import GaloisForLFunctions.RHTower.BeurlingSystemCounting

/-!
# The exact zero/one/higher large-label decomposition

Every generalized integer of a Beurling system carries a well-defined number of prime labels of
norm above a cutoff.  Splitting the Möbius-weighted exponential sum by that number gives three
absolutely convergent sectors, and the sum of the three is the full sum.  This is the first half of
the critical zero/one seam: the zero sector is the aperture sum, the one sector will be reindexed by
its unique large label, and the remaining sector is the higher-large-prime remainder.
-/

open scoped BigOperators

namespace RHTower

namespace BeurlingSystem

variable (B : BeurlingSystem)

open scoped Classical in
/-- The number of prime labels of norm above the cutoff, counted with multiplicity. -/
noncomputable def largeCount (z : ℝ) (g : Multiset B.Label) : ℕ :=
  (g.filter fun p => z < B.labelNorm p).card

/-- The Möbius-weighted exponential Gibbs term of a generalized integer. -/
noncomputable def gibbsTerm (x : ℝ) (g : Multiset B.Label) : ℝ :=
  (B.moebius g : ℝ) * Real.exp (-x * B.intNorm g)

/-- The full Möbius-weighted sum `Φ_P(x)` of `(BF3)`. -/
noncomputable def phi (x : ℝ) : ℝ := ∑' g : Multiset B.Label, B.gibbsTerm x g

/-- The zero-large-label aperture sum `A_{P,z}(x)` of `(BF3)`. -/
noncomputable def apertureSum (z x : ℝ) : ℝ :=
  ∑' g : Multiset B.Label, if B.largeCount z g = 0 then B.gibbsTerm x g else 0

/-- The one-large-label sector of `(BF4)`. -/
noncomputable def oneLargeSum (z x : ℝ) : ℝ :=
  ∑' g : Multiset B.Label, if B.largeCount z g = 1 then B.gibbsTerm x g else 0

/-- The higher-large-label remainder `R_{P,≥2,z}(x)` of `(BF4)`. -/
noncomputable def higherLargeSum (z x : ℝ) : ℝ :=
  ∑' g : Multiset B.Label, if 2 ≤ B.largeCount z g then B.gibbsTerm x g else 0

variable {B}

open scoped Classical in
theorem abs_moebius_le_one (g : Multiset B.Label) : |(B.moebius g : ℝ)| ≤ 1 := by
  rw [moebius]
  split_ifs with h
  · rw [abs_le]
    rcases Nat.even_or_odd g.card with he | ho
    · rw [he.neg_one_pow]
      norm_num
    · rw [ho.neg_one_pow]
      norm_num
  · norm_num

theorem norm_gibbsTerm_le (x : ℝ) (g : Multiset B.Label) :
    ‖B.gibbsTerm x g‖ ≤ Real.exp (-x * B.intNorm g) := by
  rw [gibbsTerm, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  have h1 := abs_moebius_le_one (B := B) g
  have h2 : (0 : ℝ) < Real.exp (-x * B.intNorm g) := Real.exp_pos _
  nlinarith

theorem summable_gibbsTerm (hdisc : B.IsDiscrete) {C : ℝ} (hC : B.HasLinearCounting C)
    {x : ℝ} (hx : 0 < x) : Summable fun g : Multiset B.Label => B.gibbsTerm x g :=
  Summable.of_norm_bounded (summable_expNegNorm hdisc hC hx) (norm_gibbsTerm_le x)

theorem summable_gibbsTerm_indicator (hdisc : B.IsDiscrete) {C : ℝ} (hC : B.HasLinearCounting C)
    {x : ℝ} (hx : 0 < x) (P : Multiset B.Label → Prop) [DecidablePred P] :
    Summable fun g : Multiset B.Label => if P g then B.gibbsTerm x g else 0 := by
  refine Summable.of_norm_bounded (summable_expNegNorm hdisc hC hx) fun g => ?_
  by_cases hg : P g
  · rw [if_pos hg]
    exact norm_gibbsTerm_le x g
  · rw [if_neg hg, norm_zero]
    exact (Real.exp_pos _).le

/-- **The exact three-sector split of `(BF4)`.**  Zero, one and at least two large labels exhaust
the generalized integers. -/
theorem phi_eq_apertureSum_add (hdisc : B.IsDiscrete) {C : ℝ} (hC : B.HasLinearCounting C)
    {x : ℝ} (hx : 0 < x) (z : ℝ) :
    B.phi x = B.apertureSum z x + B.oneLargeSum z x + B.higherLargeSum z x := by
  have h0 := summable_gibbsTerm_indicator hdisc hC hx (fun g => B.largeCount z g = 0)
  have h1 := summable_gibbsTerm_indicator hdisc hC hx (fun g => B.largeCount z g = 1)
  have h2 := summable_gibbsTerm_indicator hdisc hC hx (fun g => 2 ≤ B.largeCount z g)
  have hsplit : ∀ g : Multiset B.Label, B.gibbsTerm x g
      = ((if B.largeCount z g = 0 then B.gibbsTerm x g else 0)
          + (if B.largeCount z g = 1 then B.gibbsTerm x g else 0))
        + (if 2 ≤ B.largeCount z g then B.gibbsTerm x g else 0) := by
    intro g
    rcases Nat.lt_or_ge (B.largeCount z g) 2 with hlt | hge
    · interval_cases h : B.largeCount z g <;> norm_num
    · rw [if_neg (by omega), if_neg (by omega), if_pos hge]
      ring
  calc B.phi x
      = ∑' g : Multiset B.Label,
          (((if B.largeCount z g = 0 then B.gibbsTerm x g else 0)
              + (if B.largeCount z g = 1 then B.gibbsTerm x g else 0))
            + (if 2 ≤ B.largeCount z g then B.gibbsTerm x g else 0)) := by
        rw [phi]
        exact tsum_congr hsplit
    _ = B.apertureSum z x + B.oneLargeSum z x + B.higherLargeSum z x := by
        rw [(h0.add h1).tsum_add h2, h0.tsum_add h1, apertureSum, oneLargeSum, higherLargeSum]


/-! ## The one-large-label sector -/

theorem intNorm_cons (p : B.Label) (m : Multiset B.Label) :
    B.intNorm (p ::ₘ m) = B.labelNorm p * B.intNorm m := by
  rw [intNorm, intNorm, Multiset.map_cons, Multiset.prod_cons]

theorem largeCount_eq_zero_iff (z : ℝ) (g : Multiset B.Label) :
    B.largeCount z g = 0 ↔ ∀ q ∈ g, B.labelNorm q ≤ z := by
  classical
  rw [largeCount, Multiset.card_eq_zero, Multiset.filter_eq_nil]
  constructor
  · intro h q hq
    exact not_lt.mp (h q hq)
  · intro h q hq
    exact not_lt.mpr (h q hq)

theorem largeCount_cons (z : ℝ) {p : B.Label} (hp : z < B.labelNorm p)
    {m : Multiset B.Label} (hm : ∀ q ∈ m, B.labelNorm q ≤ z) :
    B.largeCount z (p ::ₘ m) = 1 := by
  classical
  have hfil : (m.filter fun q => z < B.labelNorm q) = 0 := by
    rw [Multiset.filter_eq_nil]
    exact fun q hq => not_lt.mpr (hm q hq)
  rw [largeCount, Multiset.filter_cons_of_pos (p := fun q => z < B.labelNorm q) m hp, hfil]
  simp

theorem exists_cons_of_largeCount_eq_one (z : ℝ) {g : Multiset B.Label}
    (hg : B.largeCount z g = 1) :
    ∃ p : B.Label, ∃ m : Multiset B.Label,
      z < B.labelNorm p ∧ (∀ q ∈ m, B.labelNorm q ≤ z) ∧ g = p ::ₘ m := by
  classical
  obtain ⟨p, hp⟩ := Multiset.card_eq_one.mp hg
  refine ⟨p, g.filter fun q => ¬ z < B.labelNorm q, ?_, ?_, ?_⟩
  · have hmem : p ∈ g.filter fun q => z < B.labelNorm q := by
      rw [hp]
      exact Multiset.mem_singleton_self p
    exact (Multiset.mem_filter.mp hmem).2
  · intro q hq
    exact not_lt.mp (Multiset.mem_filter.mp hq).2
  · have hfa := Multiset.filter_add_not (fun q => z < B.labelNorm q) g
    rw [hp] at hfa
    conv_lhs => rw [← hfa]
    rw [Multiset.singleton_add]

theorem gibbsTerm_cons (x z : ℝ) {p : B.Label} (hp : z < B.labelNorm p)
    {m : Multiset B.Label} (hm : ∀ q ∈ m, B.labelNorm q ≤ z) :
    B.gibbsTerm x (p ::ₘ m) = -B.gibbsTerm (B.labelNorm p * x) m := by
  have hpm : p ∉ m := by
    intro hmem
    exact absurd (hm p hmem) (not_le.mpr hp)
  rw [gibbsTerm, gibbsTerm, B.moebius_cons_of_notMem hpm, intNorm_cons,
    show -x * (B.labelNorm p * B.intNorm m) = -(B.labelNorm p * x) * B.intNorm m from by ring]
  push_cast
  ring

/-- The aperture sum as a sum over the small-support generalized integers. -/
theorem apertureSum_eq_tsum_subtype (z y : ℝ) :
    B.apertureSum z y
      = ∑' m : ({m : Multiset B.Label | ∀ q ∈ m, B.labelNorm q ≤ z} : Set (Multiset B.Label)),
          B.gibbsTerm y (m : Multiset B.Label) := by
  classical
  rw [apertureSum, tsum_subtype {m : Multiset B.Label | ∀ q ∈ m, B.labelNorm q ≤ z}]
  refine tsum_congr fun g => ?_
  by_cases hg : g ∈ {m : Multiset B.Label | ∀ q ∈ m, B.labelNorm q ≤ z}
  · rw [if_pos ((largeCount_eq_zero_iff z g).mpr hg), Set.indicator_of_mem hg]
  · rw [if_neg fun h => hg ((largeCount_eq_zero_iff z g).mp h), Set.indicator_of_notMem hg]

/-- **The one-large-label sector `(BF4)`.**  Writing a generalized integer with exactly one large
label as `p · m` reindexes the sector by its large label, and the generalized Möbius sign flip turns
the sector into the negative of the dilated aperture sums. -/
theorem oneLargeSum_eq_neg_tsum (hdisc : B.IsDiscrete) {C : ℝ} (hC : B.HasLinearCounting C)
    {x : ℝ} (hx : 0 < x) (z : ℝ) :
    B.oneLargeSum z x
      = -∑' p : {p : B.Label // z < B.labelNorm p},
          B.apertureSum z (B.labelNorm (p : B.Label) * x) := by
  classical
  set Large := {p : B.Label // z < B.labelNorm p}
  set Small := ({m : Multiset B.Label | ∀ q ∈ m, B.labelNorm q ≤ z} : Set (Multiset B.Label))
  set Ψ : Large × ↥Small → Multiset B.Label := fun pm => (pm.1 : B.Label) ::ₘ (pm.2 : Multiset B.Label)
    with hΨ
  set F : Multiset B.Label → ℝ := fun g => if B.largeCount z g = 1 then B.gibbsTerm x g else 0
    with hF
  have hinj : Function.Injective Ψ := by
    rintro ⟨⟨p₁, hp₁⟩, ⟨m₁, hm₁⟩⟩ ⟨⟨p₂, hp₂⟩, ⟨m₂, hm₂⟩⟩ hEq
    simp only [hΨ] at hEq
    have hfil : ∀ (p : B.Label) (m : Multiset B.Label), z < B.labelNorm p →
        (∀ q ∈ m, B.labelNorm q ≤ z) →
        ((p ::ₘ m).filter fun q => z < B.labelNorm q) = {p} := by
      intro p m hp hm
      have hnil : (m.filter fun q => z < B.labelNorm q) = 0 := by
        rw [Multiset.filter_eq_nil]
        exact fun q hq => not_lt.mpr (hm q hq)
      rw [Multiset.filter_cons_of_pos (p := fun q => z < B.labelNorm q) m hp, hnil]
      rfl
    have h1 := hfil p₁ m₁ hp₁ hm₁
    have h2 := hfil p₂ m₂ hp₂ hm₂
    rw [hEq, h2] at h1
    have hp : p₁ = p₂ := (Multiset.singleton_inj.mp h1.symm)
    subst hp
    have hm : m₁ = m₂ := (Multiset.cons_inj_right p₁).mp hEq
    subst hm
    rfl
  have hsupp : Function.support F ⊆ Set.range Ψ := by
    intro g hg
    have hcount : B.largeCount z g = 1 := by
      by_contra hcon
      exact hg (by rw [hF]; exact if_neg hcon)
    obtain ⟨p, m, hp, hm, rfl⟩ := exists_cons_of_largeCount_eq_one z hcount
    exact ⟨(⟨p, hp⟩, ⟨m, hm⟩), rfl⟩
  have hterm : ∀ pm : Large × ↥Small, F (Ψ pm)
      = -B.gibbsTerm (B.labelNorm (pm.1 : B.Label) * x) (pm.2 : Multiset B.Label) := by
    rintro ⟨⟨p, hp⟩, ⟨m, hm⟩⟩
    rw [hF, hΨ]
    simp only
    rw [if_pos (largeCount_cons z hp hm), gibbsTerm_cons x z hp hm]
  have hsummable : Summable fun pm : Large × ↥Small => F (Ψ pm) := by
    have hFsum : Summable F := summable_gibbsTerm_indicator hdisc hC hx _
    exact hFsum.comp_injective hinj
  have hsumSmall : ∀ p : Large, Summable fun m : ↥Small =>
      F (Ψ (p, m)) := by
    intro p
    have hsub : Function.Injective fun m : ↥Small => (p, m) := by
      intro m₁ m₂ h
      exact congrArg Prod.snd h
    exact hsummable.comp_injective hsub
  calc B.oneLargeSum z x = ∑' g : Multiset B.Label, F g := by rw [oneLargeSum, hF]
    _ = ∑' pm : Large × ↥Small, F (Ψ pm) := (hinj.tsum_eq hsupp).symm
    _ = ∑' p : Large, ∑' m : ↥Small, F (Ψ (p, m)) := hsummable.tsum_prod' hsumSmall
    _ = ∑' p : Large, ∑' m : ↥Small,
          -B.gibbsTerm (B.labelNorm (p : B.Label) * x) (m : Multiset B.Label) := by
        exact tsum_congr fun p => tsum_congr fun m => hterm (p, m)
    _ = -∑' p : Large, B.apertureSum z (B.labelNorm (p : B.Label) * x) := by
        rw [← tsum_neg]
        exact tsum_congr fun p => by
          rw [apertureSum_eq_tsum_subtype, ← tsum_neg]


/-- **The exact zero/one-large-prime decomposition `(BF4)`.**  Unique factorization in the free
label monoid splits the Möbius-weighted exponential sum into the aperture sum, the negative of its
dilates along the large labels, and the higher-large-label remainder. -/
theorem phi_eq_apertureSum_sub_tsum_add (hdisc : B.IsDiscrete) {C : ℝ}
    (hC : B.HasLinearCounting C) {x : ℝ} (hx : 0 < x) (z : ℝ) :
    B.phi x
      = B.apertureSum z x
        - (∑' p : {p : B.Label // z < B.labelNorm p},
            B.apertureSum z (B.labelNorm (p : B.Label) * x))
        + B.higherLargeSum z x := by
  rw [phi_eq_apertureSum_add hdisc hC hx z, oneLargeSum_eq_neg_tsum hdisc hC hx z]
  ring

end BeurlingSystem

end RHTower
