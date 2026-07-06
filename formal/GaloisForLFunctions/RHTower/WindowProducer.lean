import GaloisForLFunctions.RHTower.WindowSeam

/-!
# The window producer interface: cofinal line-data packages decide the ladder

Two bricks.  First, the **alternation chain**: a family of `s` disjoint strict sign brackets for
a real function composes into a single strictly increasing chain of `s + 1` points whose
consecutive products are all strictly negative — the exact sign-table shape the window seam
consumes; the chain is built by one pass, taking from each bracket the endpoint whose sign
opposes the current chain end (the discarded endpoint shares the chain end's sign, so the other
endpoint of its strict bracket opposes it).  Second, the **cofinal producer interface**: the
per-window line-data package (EM remainder bound, `emCarrier`/`gN` closeness, LOW floor, sign
table, count budget) on a cofinal family of heights forces every certificate at every height by
monotonicity, hence every ladder rung, hence RH.  The open analytic content is exactly the
supply of the packages; everything downstream of them is machine-checked.
-/

namespace RHTower

open Complex Set Metric

/-! ## The alternation chain -/

open Classical in
/-- The alternation chain through a family of sign brackets: starts with the first bracket, then
takes from each subsequent bracket the endpoint whose sign opposes the current chain end. -/
noncomputable def altChain (F : ℝ → ℝ) (u v : ℕ → ℝ) : ℕ → ℝ
  | 0 => u 0
  | (i + 1) =>
      if i = 0 then v 0
      else if F (altChain F u v i) * F (u i) < 0 then u i else v i

theorem altChain_zero (F : ℝ → ℝ) (u v : ℕ → ℝ) : altChain F u v 0 = u 0 := rfl

theorem altChain_one (F : ℝ → ℝ) (u v : ℕ → ℝ) : altChain F u v 1 = v 0 := by
  simp [altChain]

theorem altChain_succ_mem (F : ℝ → ℝ) (u v : ℕ → ℝ) (i : ℕ) (hi : 1 ≤ i) :
    altChain F u v (i + 1) = u i ∨ altChain F u v (i + 1) = v i := by
  have hne : ¬ i = 0 := by omega
  rw [show altChain F u v (i + 1)
      = if i = 0 then v 0 else if F (altChain F u v i) * F (u i) < 0 then u i else v i
      from rfl,
    if_neg hne]
  split_ifs with h
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Every chain point is a bracket endpoint of the matching bracket. -/
theorem altChain_mem (F : ℝ → ℝ) (u v : ℕ → ℝ) (i : ℕ) :
    (i = 0 ∧ altChain F u v i = u 0) ∨
      (1 ≤ i ∧ (altChain F u v i = u (i - 1) ∨ altChain F u v i = v (i - 1))) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · exact Or.inl ⟨rfl, altChain_zero F u v⟩
  · right
    refine ⟨hi, ?_⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · exact Or.inr (altChain_one F u v)
    · have := altChain_succ_mem F u v j hj
      simpa [Nat.add_sub_cancel, Nat.add_comm] using this

/-- **The alternation invariant**: consecutive chain products are strictly negative through the
first `s` brackets. -/
theorem altChain_alternates {F : ℝ → ℝ} {u v : ℕ → ℝ} {s : ℕ}
    (hsign : ∀ i, i < s → F (u i) * F (v i) < 0) :
    ∀ i, i < s → F (altChain F u v i) * F (altChain F u v (i + 1)) < 0 := by
  intro i
  induction i with
  | zero =>
    intro h0
    rw [altChain_zero, altChain_one]
    exact hsign 0 h0
  | succ i ih =>
    intro hi
    have hprev : F (altChain F u v i) * F (altChain F u v (i + 1)) < 0 :=
      ih (by omega)
    have hcur : F (u (i + 1)) * F (v (i + 1)) < 0 := hsign (i + 1) hi
    have hne : ¬ (i + 1) = 0 := by omega
    rw [show altChain F u v (i + 1 + 1)
        = if (i + 1) = 0 then v 0
          else if F (altChain F u v (i + 1)) * F (u (i + 1)) < 0 then u (i + 1) else v (i + 1)
        from rfl,
      if_neg hne]
    split_ifs with h
    · exact h
    · -- the chain end and u (i+1) share a sign; the bracket then forces v (i+1) to oppose
      have hendne : F (altChain F u v (i + 1)) ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hprev
        exact lt_irrefl 0 hprev
      have hune : F (u (i + 1)) ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hcur
        exact lt_irrefl 0 hcur
      have hpos : 0 < F (altChain F u v (i + 1)) * F (u (i + 1)) :=
        lt_of_le_of_ne (not_lt.mp h) (by
          intro heq
          rcases mul_eq_zero.mp heq.symm with h1 | h1
          · exact hendne h1
          · exact hune h1)
      by_contra hge
      have hge' : 0 ≤ F (altChain F u v (i + 1)) * F (v (i + 1)) := not_lt.mp hge
      have hkey : (F (altChain F u v (i + 1)) * F (u (i + 1)))
          * (F (u (i + 1)) * F (v (i + 1))) < 0 :=
        mul_neg_of_pos_of_neg hpos hcur
      have hid : (F (altChain F u v (i + 1)) * F (u (i + 1)))
          * (F (u (i + 1)) * F (v (i + 1)))
          = (F (altChain F u v (i + 1)) * F (v (i + 1)))
            * (F (u (i + 1)) * F (u (i + 1))) := by ring
      rw [hid] at hkey
      linarith [mul_nonneg hge' (mul_self_nonneg (F (u (i + 1))))]

/-- **Monotonicity of the chain** for separated ordered brackets. -/
theorem altChain_strictMono {F : ℝ → ℝ} {u v : ℕ → ℝ} {s : ℕ}
    (hord : ∀ i, i < s → u i < v i)
    (hsep : ∀ i, i + 1 < s → v i < u (i + 1)) :
    ∀ i, i < s → altChain F u v i < altChain F u v (i + 1) := by
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · rw [altChain_zero, altChain_one]
    exact hord 0 hi
  · -- chain point i is an endpoint of bracket i−1, chain point i+1 of bracket i
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hipos
    have hj1 : 1 + j - 1 = j := by omega
    have hupper : altChain F u v (1 + j) ≤ v j := by
      rcases altChain_mem F u v (1 + j) with ⟨h0, -⟩ | ⟨-, hmem⟩
      · omega
      · rw [hj1] at hmem
        rcases hmem with h | h
        · rw [h]
          exact (hord j (by omega)).le
        · rw [h]
    have hlower : u (1 + j) ≤ altChain F u v (1 + j + 1) := by
      have hmem := altChain_succ_mem F u v (1 + j) (by omega)
      rcases hmem with h | h
      · rw [h]
      · rw [h]
        exact (hord (1 + j) hi).le
    have hmid : v j < u (1 + j) := by
      have := hsep j (by omega)
      simpa [Nat.add_comm] using this
    linarith

/-- **Alternation chain from disjoint strict sign brackets.**  `s` ordered, separated, strict
sign brackets for `F` yield a strictly increasing chain of `s + 1` points, each an endpoint of
the matching bracket, whose `s` consecutive products are all strictly negative — the sign-table
shape consumed by the window seam. -/
theorem exists_alternation_chain_of_strict_brackets {F : ℝ → ℝ} {s : ℕ} {u v : ℕ → ℝ}
    (hord : ∀ i, i < s → u i < v i)
    (hsep : ∀ i, i + 1 < s → v i < u (i + 1))
    (hsign : ∀ i, i < s → F (u i) * F (v i) < 0) :
    ∃ ts : ℕ → ℝ,
      (∀ i, i < s → ts i < ts (i + 1)) ∧
      (∀ i, i < s → F (ts i) * F (ts (i + 1)) < 0) ∧
      ts 0 = u 0 ∧
      (∀ i, 1 ≤ i → i ≤ s → ts i = u (i - 1) ∨ ts i = v (i - 1)) := by
  refine ⟨altChain F u v, altChain_strictMono hord hsep, altChain_alternates hsign,
    altChain_zero F u v, ?_⟩
  intro i hi _
  rcases altChain_mem F u v i with ⟨h0, -⟩ | ⟨-, hmem⟩
  · omega
  · exact hmem

/-! ## The cofinal producer interface -/

/-- **The per-window line-data package**: every ξ-zero of the height-`T` box window is covered
by one LOW-floor EM sign certificate — EM remainder bound, `emCarrier`/`gN` closeness, LOW floor
on the annulus charts, a strict ξ sign table on the line segment, and a finite-side count budget
dominating the enclosed total.  This is the exact hypothesis family of the window-seam weld; the
open analytic content of the producer is its supply. -/
def WindowLinePackage (T : ℝ) : Prop :=
  ∀ ρ ∈ boxZeros T,
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
      (∑ z ∈ t₂, m₂ z ≤ s)

/-- An on-line ball cover produces the line-package interface vacuously.  Each candidate
right-half zero in the box is covered by a ball whose ξ-zeros are on the critical line, so no such
candidate exists; the per-zero package has an empty domain. -/
theorem windowLinePackage_of_ball_online_cover {T : ℝ}
    (h : ∀ ρ ∈ boxZeros T, ∃ a R, ρ ∈ ball a R ∧
      ∀ p ∈ ball a R, xi p = 0 → p.re = 1 / 2) :
    WindowLinePackage T := by
  intro ρ hρ
  obtain ⟨a, R, hball, honline⟩ := h ρ hρ
  exact False.elim ((ne_of_gt hρ.1.1) (honline ρ hball hρ.2))

/-- The package forces the height-`T` certificate at every level. -/
theorem windowCertificate_of_windowLinePackage {k : ℕ} {T : ℝ}
    (h : WindowLinePackage T) : WindowCertificate k T :=
  windowCertificate_of_emCarrier_sign_certificates h

/-- The package empties the window: RH below height `T`. -/
theorem boxZeros_empty_of_windowLinePackage {T : ℝ}
    (h : WindowLinePackage T) : boxZeros T = ∅ :=
  boxZeros_empty_of_emCarrier_sign_certificates h

/-- **The cofinal producer, ladder form**: line-data packages on a cofinal family of heights
force every rung. -/
theorem rhLadder_of_cofinal_windowLinePackages {k : ℕ}
    (h : ∀ N : ℝ, ∃ T, N ≤ T ∧ WindowLinePackage T) : RHLadder k := by
  refine rhLadder_of_cofinal_windowCertificates ?_
  intro N
  obtain ⟨T, hT, hp⟩ := h N
  exact ⟨T, hT, windowCertificate_of_windowLinePackage hp⟩

/-- **The cofinal producer, RH form**: line-data packages on a cofinal family of heights give
the Riemann Hypothesis.  Everything below the packages is machine-checked; the open analytic
content of the producer program is exactly their supply. -/
theorem rh_of_cofinal_windowLinePackages
    (h : ∀ N : ℝ, ∃ T, N ≤ T ∧ WindowLinePackage T) : RiemannHypothesis := by
  rw [rh_iff_forall_ladder]
  exact fun _ => rhLadder_of_cofinal_windowLinePackages h

end RHTower
