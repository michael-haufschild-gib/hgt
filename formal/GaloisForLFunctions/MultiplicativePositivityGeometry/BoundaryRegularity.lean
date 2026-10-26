import GaloisForLFunctions.MultiplicativePositivityGeometry.BoundaryDivisorRange
import GaloisForLFunctions.MultiplicativePositivityGeometry.SimplePoleClassification

/-!
# Boundary regularity: the simple-pole classification without local finiteness

A boundary divisor is a pointwise limit of continuous functions
(`exists_posCosPoly_of_isBoundaryDivisor`). By Baire's theorem such a limit stays within `1/4` of
one continuous function on a nonempty open set (`exists_open_near_continuous`), so it cannot jump
by `1` between two dense sets (`not_tendsto_continuous_of_dense`).

**Classification** (`boundary_tetrachotomy`). Let `D` be an integer boundary divisor with
`D(0) = 1`. Its nonvanishing set is a subgroup `H` of `ℝ` on which `D` is a `±1` character.

* `H` cyclic: `D` is locally finite and the trichotomy applies.
* `H` dense and proper: `D = ±1` on `H` and `D = 0` on the dense translate `H + a`, `a ∉ H`, which
  regularity forbids.
* `H = ℝ`: `D(u) = D(u/2)² = 1`.

So `D` is `δ₀`, a lattice indicator, an alternating lattice character or the constant `1`
(`const_isBoundaryDivisor`), and every other integer simple-pole boundary divisor is locally finite
(`boundary_locallyFinite`). Regularity is a forcing mechanism of its own: positive definiteness
permits the indicator of every subgroup, boundary limits permit only closed ones.
-/

open Filter Topology

namespace GaloisForLFunctions.MultiplicativePositivityGeometry

/-- **Baire.** A pointwise limit of continuous functions is within `1/4` of one of them on a
nonempty open set. -/
theorem exists_open_near_continuous {f : ℕ → ℝ → ℝ} (hf : ∀ n, Continuous (f n)) {g : ℝ → ℝ}
    (hlim : ∀ u, Tendsto (fun n => f n u) atTop (𝓝 (g u))) :
    ∃ N, ∃ U : Set ℝ, IsOpen U ∧ U.Nonempty ∧ ∀ u ∈ U, |g u - f N u| ≤ 1 / 4 := by
  set A : ℕ → Set ℝ := fun N => ⋂ n ≥ N, {u | |f n u - f N u| ≤ 1 / 4}
  have hA : ∀ N, IsClosed (A N) := fun N =>
    isClosed_biInter fun n _ => isClosed_le ((hf n).sub (hf N)).abs continuous_const
  have hU : ⋃ N, A N = Set.univ := by
    refine Set.eq_univ_of_forall fun u => Set.mem_iUnion.mpr ?_
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hlim u) (1 / 8) (by norm_num)
    refine ⟨N, Set.mem_iInter₂.mpr fun n hn => ?_⟩
    have h1 := hN n hn
    have h2 := hN N le_rfl
    rw [Real.dist_eq] at h1 h2
    show |f n u - f N u| ≤ 1 / 4
    calc |f n u - f N u| = |(f n u - g u) - (f N u - g u)| := by rw [sub_sub_sub_cancel_right]
      _ ≤ |f n u - g u| + |f N u - g u| := abs_sub _ _
      _ ≤ 1 / 4 := by linarith
  obtain ⟨N, hint⟩ := nonempty_interior_of_iUnion_of_closed hA hU
  refine ⟨N, interior (A N), isOpen_interior, hint, fun u hu => ?_⟩
  have hmem : u ∈ A N := interior_subset hu
  have hev : ∀ᶠ n in atTop, |f n u - f N u| ≤ 1 / 4 :=
    eventually_atTop.mpr ⟨N, fun n hn => Set.mem_iInter₂.mp hmem n hn⟩
  exact le_of_tendsto (((hlim u).sub_const (f N u)).abs) hev

/-- **Regularity obstruction.** A function with `|g| ≥ 1` on a dense set and `g = 0` on another
dense set is not a pointwise limit of continuous functions. -/
theorem not_tendsto_continuous_of_dense {f : ℕ → ℝ → ℝ} (hf : ∀ n, Continuous (f n)) {g : ℝ → ℝ}
    (hlim : ∀ u, Tendsto (fun n => f n u) atTop (𝓝 (g u))) {S T : Set ℝ} (hS : Dense S)
    (hT : Dense T) (hgS : ∀ u ∈ S, 1 ≤ |g u|) (hgT : ∀ u ∈ T, g u = 0) : False := by
  obtain ⟨N, U, hUo, hUne, hclose⟩ := exists_open_near_continuous hf hlim
  obtain ⟨q, hqS, hqU⟩ := hS.exists_mem_open hUo hUne
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuous_iff.mp (hf N) q (1 / 4) (by norm_num)
  obtain ⟨v, hvT, hvU⟩ := hT.exists_mem_open (hUo.inter Metric.isOpen_ball)
    ⟨q, hqU, Metric.mem_ball_self hδ⟩
  have h1 := abs_le.mp (hclose q hqU)
  have h2 := hclose v hvU.1
  rw [hgT v hvT, zero_sub, abs_neg] at h2
  have h3 := hδc v hvU.2
  rw [Real.dist_eq] at h3
  have h2' := abs_le.mp h2
  have h3' := abs_lt.mp h3
  rcases le_abs'.mp (hgS q hqS) with h | h <;> linarith [h1.1, h1.2, h2'.1, h2'.2, h3'.1, h3'.2]

/-- The constant `1` is a boundary divisor: one frequency `0` with weight `1/x`. -/
theorem const_isBoundaryDivisor :
    IsBoundaryDivisor (fun _ : Unit => (0 : ℝ)) (fun x _ => 1 / x) (fun _ => 1) where
  nonneg x hx _ := by positivity
  summable _ _ := Summable.of_finite
  tendsto u := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp [cosineTrace, (Set.mem_Ioi.mp hx).ne']

variable {ι : Type*} {lam : ι → ℝ} {w : ℝ → ι → ℝ} {D : ℝ → ℝ}

/-- The nonvanishing subgroup of an integer simple-pole boundary divisor is cyclic or all of `ℝ`. -/
theorem nonvanishing_cyclic_or_univ (hw : IsBoundaryDivisor lam w D) (h0 : D 0 = 1)
    (hint : ∀ u, ∃ n : ℤ, D u = n) :
    (∃ a : ℝ, ∀ u, D u ≠ 0 → ∃ k : ℤ, u = k * a) ∨ ∀ u, D u ≠ 0 := by
  have hD := hw.isEvenPosDef
  rcases (nonvanishingSubgroup hD h0 hint).dense_or_cyclic with hdense | ⟨a, ha⟩
  · by_contra hcon
    push Not at hcon
    obtain ⟨a, ha⟩ := hcon.2
    -- `D = ±1` on the dense subgroup and `D = 0` on its dense translate by `a`.
    set H : Set ℝ := (nonvanishingSubgroup hD h0 hint : Set ℝ)
    have hT : Dense ((fun v => v - a) ⁻¹' H) := hdense.preimage (Homeomorph.subRight a).isOpenMap
    obtain ⟨P, hP, hlim⟩ := exists_posCosPoly_of_isBoundaryDivisor hw
    refine not_tendsto_continuous_of_dense (fun n => (hP n).continuous) hlim hdense hT
      (fun u hu => ?_) (fun v hv => ?_)
    · rcases boundary_values hD h0 hint u with h | h | h
      · rw [h]; norm_num
      · exact absurd h hu
      · rw [h]; norm_num
    · by_contra hne
      have hvH : v ∈ nonvanishingSubgroup hD h0 hint := hne
      have : a ∈ nonvanishingSubgroup hD h0 hint := by
        simpa using (nonvanishingSubgroup hD h0 hint).sub_mem hvH hv
      exact this ha
  · left
    refine ⟨a, fun u hu => ?_⟩
    have hmem : u ∈ nonvanishingSubgroup hD h0 hint := hu
    rw [ha, ← AddSubgroup.zmultiples_eq_closure, AddSubgroup.mem_zmultiples_iff] at hmem
    obtain ⟨k, hk⟩ := hmem
    exact ⟨k, by rw [← hk, zsmul_eq_mul]⟩

/-- **Integer simple-pole boundary divisors are locally finite or constant.** -/
theorem boundary_locallyFinite (hw : IsBoundaryDivisor lam w D) (h0 : D 0 = 1)
    (hint : ∀ u, ∃ n : ℤ, D u = n) :
    (∀ T, {u : ℝ | |u| ≤ T ∧ D u ≠ 0}.Finite) ∨ ∀ u, D u = 1 := by
  have hD := hw.isEvenPosDef
  rcases nonvanishing_cyclic_or_univ hw h0 hint with ⟨a, hmem⟩ | htop
  · left
    intro T
    rcases eq_or_ne a 0 with rfl | ha0
    · refine (Set.finite_singleton (0 : ℝ)).subset fun u hu => ?_
      obtain ⟨k, hk⟩ := hmem u hu.2
      simp [hk]
    · refine ((Finset.Icc (-⌈T / |a|⌉) ⌈T / |a|⌉).finite_toSet.image
        (fun k : ℤ => (k : ℝ) * a)).subset fun u hu => ?_
      obtain ⟨k, rfl⟩ := hmem u hu.2
      refine ⟨k, ?_, rfl⟩
      have hk : |(k : ℝ)| ≤ T / |a| := by
        rw [le_div_iff₀ (abs_pos.mpr ha0), ← abs_mul]; exact hu.1
      obtain ⟨h1, h2⟩ := abs_le.mp (hk.trans (Int.le_ceil _))
      simp only [Finset.coe_Icc, Set.mem_Icc]
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · right
    intro u
    have hmul := intValued_mul hD h0 hint (htop (u / 2)) (u / 2)
    rw [add_halves] at hmul
    rcases boundary_values hD h0 hint (u / 2) with h | h | h
    · rw [hmul, h]; norm_num
    · exact absurd h (htop _)
    · rw [hmul, h]; norm_num

open Classical in
/-- **The simple-pole classification without local finiteness.** An integer boundary divisor with
`D(0) = 1` is `δ₀`, the indicator of a lattice `cℤ`, the alternating character on `cℤ`, or the
constant `1`; each type occurs. -/
theorem boundary_tetrachotomy (hw : IsBoundaryDivisor lam w D) (h0 : D 0 = 1)
    (hint : ∀ u, ∃ n : ℤ, D u = n) :
    (∀ u, D u = if u = 0 then 1 else 0) ∨
    (∃ c > 0, ∀ u, D u = if ∃ k : ℤ, u = k * c then 1 else 0) ∨
    (∃ c > 0, (∀ k : ℤ, D (k * c) = (-1) ^ k.natAbs) ∧
      ∀ u, (¬ ∃ k : ℤ, u = k * c) → D u = 0) ∨
    (∀ u, D u = 1) := by
  rcases boundary_locallyFinite hw h0 hint with hfin | hone
  · rcases boundary_trichotomy hw.isEvenPosDef h0 hint hfin with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr hone))

end GaloisForLFunctions.MultiplicativePositivityGeometry
