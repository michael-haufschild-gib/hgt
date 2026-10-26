import GaloisForLFunctions.MultiplicativePositivityGeometry.FamilyLocallyFinite
import GaloisForLFunctions.MultiplicativePositivityGeometry.BoundaryRegularity

/-!
# Regularity of family divisors: the integer simple-pole classification for families

Let `𝒟` be an integer joint boundary divisor of a family over a finite abelian group `G`, with
`𝒟(0) = 1`. No pole isolation is assumed.

* **The origin fibre is a boundary divisor** (`originFibre_isBoundaryDivisor`): at `g = 0` the joint
  trace is the cosine trace of the same weights, so `u ↦ 𝒟(0, u)` falls under the simple-pole
  classification without local finiteness (`boundary_locallyFinite`).
* **Dichotomy** (`joint_locallyFinite_or_fibreConstant`). Either `𝒟` is locally finite on `G × ℝ`, or
  `𝒟(g, u) = 𝒟(g, 0)` for all `g, u`. The nonvanishing set is a subgroup, so each fibre is a coset
  of the origin fibre's support; a constant origin fibre `𝒟(0, ·) = 1` propagates by
  multiplicativity.
* **Classification** (`joint_integer_classification`). An integer configuration with `𝒟(0) = 1` is a
  joint boundary divisor iff it is positive definite and either locally finite or constant along
  the fibres; the locally finite ones are realized by the family Bochner theorem, the fibre-constant
  ones by weights at frequency `0`.
-/

open Finset Filter Topology Complex

namespace GaloisForLFunctions.MultiplicativePositivityGeometry

universe u

variable {G : Type u} [AddCommGroup G] [Fintype G] [DecidableEq G]

omit [Fintype G] [DecidableEq G] in
/-- At `g = 0` a joint mode is a cosine. -/
theorem jointMode_origin (ψ : AddChar G ℂ) (lam u : ℝ) :
    jointMode ψ lam (0, u) = Real.cos (lam * u) := by
  simp only [jointMode, jointPhase, AddChar.map_zero_eq_one, one_mul]
  exact Complex.exp_ofReal_mul_I_re (lam * u)

omit [Fintype G] [DecidableEq G] in
/-- **The origin fibre of a joint divisor is a boundary divisor of the same weights.** -/
theorem originFibre_isBoundaryDivisor {ι : Type*} {ψ : ι → AddChar G ℂ} {lam : ι → ℝ}
    {w : ℝ → ι → ℝ} {𝒟 : G × ℝ → ℝ} (hw : IsJointBoundaryDivisor ψ lam w 𝒟) :
    IsBoundaryDivisor lam w fun u => 𝒟 (0, u) where
  nonneg := hw.nonneg
  summable := hw.summable
  tendsto u := by
    refine (hw.tendsto (0, u)).congr fun x => ?_
    unfold jointTrace cosineTrace
    simp only [jointMode_origin]

omit [DecidableEq G] in
/-- **Dichotomy.** An integer joint divisor with `𝒟(0) = 1` is locally finite or constant along the
fibres. -/
theorem joint_locallyFinite_or_fibreConstant {ι : Type*} {ψ : ι → AddChar G ℂ} {lam : ι → ℝ}
    {w : ℝ → ι → ℝ} {𝒟 : G × ℝ → ℝ} (hw : IsJointBoundaryDivisor ψ lam w 𝒟) (h0 : 𝒟 0 = 1)
    (hint : ∀ p, ∃ n : ℤ, 𝒟 p = n) :
    (∀ R : ℝ, {p : G × ℝ | 𝒟 p ≠ 0 ∧ |p.2| ≤ R}.Finite) ∨ ∀ g u, 𝒟 (g, u) = 𝒟 (g, 0) := by
  classical
  have hD := hw.isEvenPosDef
  have hfib := originFibre_isBoundaryDivisor hw
  rcases boundary_locallyFinite hfib (show 𝒟 ((0 : G), (0 : ℝ)) = 1 from h0) (fun u => hint (0, u))
    with hfin | hone
  · left
    intro R
    -- Each fibre lies in a translate of the origin fibre's support.
    have hfibre : ∀ g : G, {u : ℝ | 𝒟 (g, u) ≠ 0 ∧ |u| ≤ R}.Finite := by
      intro g
      by_cases hne : ∃ u₀, 𝒟 (g, u₀) ≠ 0 ∧ |u₀| ≤ R
      · obtain ⟨u₀, hu₀, hu₀R⟩ := hne
        refine ((hfin (2 * R)).image fun v => v + u₀).subset fun u hu => ?_
        refine ⟨u - u₀, ⟨?_, ?_⟩, by ring⟩
        · have := abs_sub u u₀
          linarith [hu.2, hu₀R]
        · have hmem1 : (g, u) ∈ nonvanishingSubgroup hD h0 hint := hu.1
          have hmem2 : (g, u₀) ∈ nonvanishingSubgroup hD h0 hint := hu₀
          have := (nonvanishingSubgroup hD h0 hint).sub_mem hmem1 hmem2
          rw [mem_nonvanishingSubgroup, Prod.mk_sub_mk, sub_self] at this
          exact this
      · push Not at hne
        refine Set.finite_empty.subset fun u hu => ?_
        exact absurd hu.2 (not_le.mpr (hne u hu.1))
    have hcover : {p : G × ℝ | 𝒟 p ≠ 0 ∧ |p.2| ≤ R} ⊆
        ⋃ g : G, (fun u => (g, u)) '' {u : ℝ | 𝒟 (g, u) ≠ 0 ∧ |u| ≤ R} := by
      rintro ⟨g, u⟩ hp
      exact Set.mem_iUnion.mpr ⟨g, ⟨u, hp, rfl⟩⟩
    exact (Set.finite_iUnion fun g => (hfibre g).image _).subset hcover
  · right
    intro g u
    have hu : 𝒟 (0, u) ≠ 0 := by rw [hone u]; exact one_ne_zero
    have h := intValued_mul hD h0 hint hu (g, 0)
    rw [show ((0 : G), u) + (g, 0) = (g, u) by simp, hone u, one_mul] at h
    exact h

/-! ### Fibre-constant configurations -/

omit [Fintype G] [DecidableEq G] in
/-- Restricting a positive-definite function to the subgroup `G × {0}` keeps it positive definite:
its Gram forms split along the heights. -/
theorem IsEvenPosDef.restrict_zero {𝒟 : G × ℝ → ℝ} (h𝒟 : IsEvenPosDef 𝒟) :
    IsEvenPosDef fun p => if p.2 = 0 then 𝒟 p else 0 where
  even p := by simp only [Prod.snd_neg, neg_eq_zero, h𝒟.even]
  posDef n x c := by
    classical
    set V : Finset ℝ := Finset.univ.image fun i => (x i).2
    have hind : ∀ i j, (if (x i - x j).2 = 0 then (1 : ℝ) else 0) =
        ∑ v ∈ V, (if (x i).2 = v then 1 else 0) * (if (x j).2 = v then 1 else 0) := fun i j => by
      have hi : (x i).2 ∈ V := Finset.mem_image_of_mem _ (Finset.mem_univ i)
      rw [Finset.sum_congr rfl fun v _ => boole_mul _ _, Finset.sum_ite_eq, if_pos hi]
      by_cases h : (x i).2 = (x j).2
      · rw [if_pos (by rw [Prod.snd_sub, h, sub_self]), if_pos h.symm]
      · rw [if_neg (by rw [Prod.snd_sub, sub_eq_zero]; exact h), if_neg (Ne.symm h)]
    have e2 : ∀ i j, c i * c j * (if (x i - x j).2 = 0 then 𝒟 (x i - x j) else 0) =
        ∑ v ∈ V, c i * (if (x i).2 = v then 1 else 0) * (c j * (if (x j).2 = v then 1 else 0)) *
          𝒟 (x i - x j) := fun i j => by
      rw [← boole_mul, hind i j, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun v _ => by ring
    simp only [e2]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
    exact Finset.sum_nonneg fun v _ =>
      h𝒟.posDef n x fun i => c i * (if (x i).2 = v then 1 else 0)

/-- Frequency-`0` weights `B₀(ψ)/(|G| x)` for a fibre-constant configuration. -/
noncomputable def fibreWeight (𝒟 : G × ℝ → ℝ) (x : ℝ) (ψ : AddChar G ℂ) : ℝ :=
  familyBohr (fun p => if p.2 = 0 then 𝒟 p else 0) ψ 0 / Fintype.card G / x

/-- **Fibre-constant configurations are realized at frequency `0`.** -/
theorem fibreConstant_isJointBoundaryDivisor {𝒟 : G × ℝ → ℝ} (h𝒟 : IsEvenPosDef 𝒟)
    (hc : ∀ g u, 𝒟 (g, u) = 𝒟 (g, 0)) :
    IsJointBoundaryDivisor (fun ψ : AddChar G ℂ => ψ) (fun _ => 0) (fibreWeight 𝒟) 𝒟 := by
  classical
  set S₀ : Finset (G × ℝ) := Finset.univ.image fun g : G => (g, (0 : ℝ))
  have hS0 : ∀ p ∉ S₀, (if p.2 = 0 then 𝒟 p else 0) = 0 := fun p hp => by
    rw [if_neg]
    intro h
    exact hp (Finset.mem_image.mpr ⟨p.1, Finset.mem_univ _, by rw [← h]⟩)
  have hsum : Summable fun p : G × ℝ => if p.2 = 0 then 𝒟 p else 0 :=
    summable_of_ne_finset_zero hS0
  have hG0 : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  refine ⟨fun x hx ψ => div_nonneg (div_nonneg (familyBohr_nonneg h𝒟.restrict_zero hsum ψ 0)
    hG0.le) hx.le, fun x _ => Summable.of_finite, fun q => ?_⟩
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := (Set.mem_Ioi.mp hx).ne'
  have horth := sum_familyBohr_mul_jointMode hS0 0 q
  simp only [zero_mul, Real.cos_zero, mul_one] at horth
  unfold jointTrace fibreWeight
  rw [tsum_fintype, Finset.mul_sum]
  have e : ∀ ψ : AddChar G ℂ, x * (familyBohr (fun p => if p.2 = 0 then 𝒟 p else 0) ψ 0 /
      Fintype.card G / x * jointMode ψ 0 q) = 1 / (Fintype.card G : ℝ) *
        familyBohr (fun p => if p.2 = 0 then 𝒟 p else 0) ψ 0 * jointMode ψ 0 q := fun ψ => by
    field_simp
  rw [Finset.sum_congr rfl fun ψ _ => e ψ, horth, Finset.sum_image fun g _ h _ hgh => by
    simpa using hgh]
  simp only [if_true]
  -- `Σ_g 𝒟(g, 0)/2 ([q₁ = g] + [q₁ = −g]) = 𝒟(q₁, 0) = 𝒟(q)`.
  have hsplit : ∀ g : G, 𝒟 (g, 0) / 2 * ((if q.1 = g then (1 : ℝ) else 0) +
      if q.1 = -g then 1 else 0) =
      (if q.1 = g then 𝒟 (g, 0) / 2 else 0) + (if -q.1 = g then 𝒟 (g, 0) / 2 else 0) :=
    fun g => by
      have e3 : (q.1 = -g) ↔ (-q.1 = g) := by
        constructor
        · intro h; rw [h, neg_neg]
        · intro h; rw [← h, neg_neg]
      simp only [e3]
      split_ifs <;> ring
  rw [Finset.sum_congr rfl fun g _ => hsplit g, Finset.sum_add_distrib, Finset.sum_ite_eq,
    Finset.sum_ite_eq, if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]
  have hev : 𝒟 (-q.1, 0) = 𝒟 (q.1, 0) := by
    have := h𝒟.even (q.1, 0)
    simpa using this
  rw [hev, hc q.1 q.2]
  ring

omit [Fintype G] [DecidableEq G] in
/-- Reindexing a joint datum by an equivalence. -/
theorem IsJointBoundaryDivisor.comp_equiv {ι ι' : Type*} {ψ : ι → AddChar G ℂ}
    {lam : ι → ℝ} {w : ℝ → ι → ℝ} {𝒟 : G × ℝ → ℝ} (e : ι' ≃ ι)
    (h : IsJointBoundaryDivisor ψ lam w 𝒟) :
    IsJointBoundaryDivisor (ψ ∘ e) (lam ∘ e) (fun x i => w x (e i)) 𝒟 where
  nonneg x hx i := h.nonneg x hx (e i)
  summable x hx := (e.summable_iff).mpr (h.summable x hx)
  tendsto p := by
    refine (h.tendsto p).congr fun x => ?_
    unfold jointTrace
    rw [← e.tsum_eq]
    rfl

/-- **The integer simple-pole classification for families.** An integer configuration on `G × ℝ`
with `𝒟(0) = 1` is a joint boundary divisor iff it is positive definite and either locally finite
or constant along the fibres. -/
theorem joint_integer_classification {𝒟 : G × ℝ → ℝ} (h0 : 𝒟 0 = 1)
    (hint : ∀ p, ∃ n : ℤ, 𝒟 p = n) :
    (∃ (ι : Type u) (ψ : ι → AddChar G ℂ) (lam : ι → ℝ) (w : ℝ → ι → ℝ),
        IsJointBoundaryDivisor ψ lam w 𝒟) ↔
      IsEvenPosDef 𝒟 ∧ ((∀ R : ℝ, {p : G × ℝ | 𝒟 p ≠ 0 ∧ |p.2| ≤ R}.Finite) ∨
        ∀ g u, 𝒟 (g, u) = 𝒟 (g, 0)) := by
  constructor
  · rintro ⟨_, _, _, _, hw⟩
    exact ⟨hw.isEvenPosDef, joint_locallyFinite_or_fibreConstant hw h0 hint⟩
  · rintro ⟨h𝒟, hloc | hc⟩
    · obtain ⟨ι, ψ, lam, w, hw⟩ := (family_locallyFinite_bochner hloc).mpr h𝒟
      exact ⟨ULift.{u} ι, _, _, _, hw.comp_equiv Equiv.ulift⟩
    · exact ⟨_, _, _, _, fibreConstant_isJointBoundaryDivisor h𝒟 hc⟩

end GaloisForLFunctions.MultiplicativePositivityGeometry
