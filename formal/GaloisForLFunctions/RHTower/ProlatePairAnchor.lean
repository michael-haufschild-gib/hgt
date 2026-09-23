import GaloisForLFunctions.RHTower.ProlateAnchorComparison

/-!
# A common forbidden-region anchor for two rungs

The ratio of two rungs is compared at a *single* band point, so the anchor has to avoid the zeros of
both Hermite functions at once.  The product of two Hermite polynomials is again a nonzero
polynomial, so it has finitely many roots and every interval contains a point where neither factor
vanishes.

The anchor of the pair is then fixed beyond the classical turning point of the *higher* rung, so
that both modes are in their forbidden region there.
-/

noncomputable section

open Set Filter Topology

namespace RHTower

open GaloisForLFunctions.RHTower

/-- The two Hermite functions do not both vanish identically on any interval. -/
theorem exists_hermiteFun_pair_ne_zero_Ioo (m n : ℕ) {A B : ℝ} (hAB : A < B) :
    ∃ x ∈ Ioo A B, hermiteFun m x ≠ 0 ∧ hermiteFun n x ≠ 0 := by
  by_contra hcon
  set Pm : Polynomial ℝ := (Polynomial.hermite m).map (Int.castRingHom ℝ) with hPm
  set Pn : Polynomial ℝ := (Polynomial.hermite n).map (Int.castRingHom ℝ) with hPn
  have hPmmonic : Pm.Monic := (Polynomial.hermite_monic m).map _
  have hPnmonic : Pn.Monic := (Polynomial.hermite_monic n).map _
  have hprodmonic : (Pm * Pn).Monic := hPmmonic.mul hPnmonic
  have hevalm : ∀ x : ℝ, Polynomial.aeval x (Polynomial.hermite m) = Pm.eval x := by
    intro x
    rw [hPm, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    rfl
  have hevaln : ∀ x : ℝ, Polynomial.aeval x (Polynomial.hermite n) = Pn.eval x := by
    intro x
    rw [hPn, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    rfl
  have hzero : ∀ x ∈ Ioo A B, hermiteFun m x * hermiteFun n x = 0 := by
    intro x hx
    by_contra hne
    exact hcon ⟨x, hx, fun h => hne (by rw [h]; ring), fun h => hne (by rw [h]; ring)⟩
  have hroot : {y : ℝ | (Pm * Pn).IsRoot y}.Infinite := by
    have hinj : Set.InjOn (fun x : ℝ => Real.sqrt 2 * x) (Ioo A B) := by
      intro x _ y _ hxy
      have h2 : Real.sqrt 2 ≠ 0 := by positivity
      exact mul_left_cancel₀ h2 hxy
    have himg : ((fun x : ℝ => Real.sqrt 2 * x) '' Ioo A B).Infinite :=
      (Set.Ioo_infinite hAB).image hinj
    refine himg.mono ?_
    rintro y ⟨x, hx, rfl⟩
    have h := hzero x hx
    have hexp : Real.exp (-((Real.sqrt 2 * x) ^ (2 : ℕ) / 4)) ≠ 0 := (Real.exp_pos _).ne'
    have hval : (Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite m)
        * Real.exp (-((Real.sqrt 2 * x) ^ (2 : ℕ) / 4)))
        * (Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite n)
        * Real.exp (-((Real.sqrt 2 * x) ^ (2 : ℕ) / 4))) = 0 := h
    have hz : Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite m)
        * Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite n) = 0 := by
      have hfac : (Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite m)
          * Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite n))
          * (Real.exp (-((Real.sqrt 2 * x) ^ (2 : ℕ) / 4))
            * Real.exp (-((Real.sqrt 2 * x) ^ (2 : ℕ) / 4))) = 0 := by
        rw [← hval]; ring
      rcases mul_eq_zero.1 hfac with h1 | h2
      · exact h1
      · exact absurd h2 (by positivity)
    show (Pm * Pn).IsRoot (Real.sqrt 2 * x)
    rw [Polynomial.IsRoot, Polynomial.eval_mul, ← hevalm, ← hevaln]
    exact hz
  exact hprodmonic.ne_zero (Polynomial.eq_zero_of_infinite_isRoot _ hroot)

/-- A point beyond the classical turning point of the higher rung at which neither Hermite function
vanishes. -/
def prolatePairAnchor (m n : ℕ) : ℝ :=
  Classical.choose (exists_hermiteFun_pair_ne_zero_Ioo (2 * m) (2 * n)
    (A := 2 * Real.sqrt (4 * (m : ℝ) + 4 * (n : ℝ) + 1))
    (B := 2 * Real.sqrt (4 * (m : ℝ) + 4 * (n : ℝ) + 1) + 1) (by linarith))

theorem prolatePairAnchor_spec (m n : ℕ) :
    prolatePairAnchor m n ∈ Ioo (2 * Real.sqrt (4 * (m : ℝ) + 4 * (n : ℝ) + 1))
        (2 * Real.sqrt (4 * (m : ℝ) + 4 * (n : ℝ) + 1) + 1) ∧
      hermiteFun (2 * m) (prolatePairAnchor m n) ≠ 0 ∧
      hermiteFun (2 * n) (prolatePairAnchor m n) ≠ 0 :=
  Classical.choose_spec (exists_hermiteFun_pair_ne_zero_Ioo (2 * m) (2 * n)
    (A := 2 * Real.sqrt (4 * (m : ℝ) + 4 * (n : ℝ) + 1))
    (B := 2 * Real.sqrt (4 * (m : ℝ) + 4 * (n : ℝ) + 1) + 1) (by linarith))

theorem prolatePairAnchor_pos (m n : ℕ) : 0 < prolatePairAnchor m n := by
  have h := (prolatePairAnchor_spec m n).1.1
  have hs : (0 : ℝ) ≤ Real.sqrt (4 * (m : ℝ) + 4 * (n : ℝ) + 1) := Real.sqrt_nonneg _
  linarith

/-- The pair anchor is beyond twice the turning scale of each of the two rungs. -/
theorem prolatePairAnchor_sq_gt (m n : ℕ) (k : ℕ) (hk : k = m ∨ k = n) :
    4 * (4 * (k : ℝ) + 1) < prolatePairAnchor m n ^ (2 : ℕ) := by
  have h := (prolatePairAnchor_spec m n).1.1
  have hpos : 0 < prolatePairAnchor m n := prolatePairAnchor_pos m n
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hsum : (4 * (k : ℝ) + 1) ≤ 4 * (m : ℝ) + 4 * (n : ℝ) + 1 := by
    rcases hk with h | h <;> subst h <;> linarith
  have hsq : Real.sqrt (4 * (m : ℝ) + 4 * (n : ℝ) + 1) ^ (2 : ℕ)
      = 4 * (m : ℝ) + 4 * (n : ℝ) + 1 := by
    refine Real.sq_sqrt ?_
    linarith
  nlinarith [h, hsq, hsum, Real.sqrt_nonneg (4 * (m : ℝ) + 4 * (n : ℝ) + 1)]


/-- **The anchor comparison at an arbitrary positive band point.**  The proof of
`tendsto_anchor_ratio` uses only the positivity of the anchor, so it holds verbatim at any positive
rescaled point. -/
theorem tendsto_anchor_ratio_at (n : ℕ) {x₀ : ℝ} (hx : 0 < x₀) :
    Tendsto (fun a : ℝ =>
        hermiteFun (2 * n) 0
          * ((signedModeRadialData a n).R (x₀ / Real.sqrt (signedModeRadialBandwidth a))
            / (signedModeRadialData a n).R 0))
      atTop (𝓝 (hermiteFun (2 * n) x₀)) := by
  have hmem : x₀ ∈ Icc (0 : ℝ) x₀ := ⟨hx.le, le_rfl⟩
  have hbase := tendsto_indexedOscillatorProfile_hermiteRung n hx x₀ hmem
  have hmap : Filter.map (Subtype.val :
      GaloisForLFunctions.RHTower.ProlatePositiveAperture → ℝ) atTop = atTop := by
    refine Filter.map_val_atTop_of_Ici_subset (a := (1 : ℝ)) (s := {x : ℝ | 0 < x}) ?_
    intro x hx1
    have hx2 : (1 : ℝ) ≤ x := hx1
    exact lt_of_lt_of_le zero_lt_one hx2
  rw [← hmap, Filter.tendsto_map'_iff]
  exact hbase

/-- The pair anchor comparison, for both rungs at once. -/
theorem tendsto_pairAnchor_ratio (m n : ℕ) (k : ℕ) :
    Tendsto (fun a : ℝ =>
        hermiteFun (2 * k) 0
          * ((signedModeRadialData a k).R
              (prolatePairAnchor m n / Real.sqrt (signedModeRadialBandwidth a))
            / (signedModeRadialData a k).R 0))
      atTop (𝓝 (hermiteFun (2 * k) (prolatePairAnchor m n))) :=
  tendsto_anchor_ratio_at k (prolatePairAnchor_pos m n)

end RHTower

end
