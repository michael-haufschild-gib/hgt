import GaloisForLFunctions.HTGeometry.ResolventHalfPowerProfile

/-!
# The vector half-power profile and its grade-one projection

Applied to a fixed vector, the half-power profile of the resolvent is the path expansion

`Π(L)β = Σ_k binom(2k,k) 4^{-k} 2^{-k} L^{-(k+a)} Tᵏβ`,

whose `k`-th term is the totality of length-`k` adjacency words starting at `β`.  A projection that
kills `β` deletes exactly the grade-zero term and no path: the projected profile starts at `k = 1`,
so it gains one full power of `L`.  With `a = 1/2` and `L ≥ ‖T‖` this is the grade-one rate

`‖P Π(L)β‖ ≤ ‖P‖‖T‖‖β‖ L^{-3/2}`,

the exponent that puts every strict-interior descendant in `L²` and `H¹` on a terminal ray while the
unprojected profile, decaying only like `L^{-1/2}`, is in neither.
-/

open Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-! ## The vector profile -/

/-- The half-power profile applied to a vector: the `k`-th term collects the length-`k` adjacency
words issuing from `β`. -/
def resolventVecProfile (T : X →L[ℂ] X) (a : ℝ) (g : ℕ → ℝ) (L : ℝ) (β : X) : X :=
  ∑' k : ℕ, resolventCoeffG a g k L • (T ^ k) β

omit [CompleteSpace X] in
private theorem norm_pow_apply_le (T : X →L[ℂ] X) (β : X) (k : ℕ) :
    ‖(T ^ k) β‖ ≤ ‖T‖ ^ k * ‖β‖ := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp
  · calc ‖(T ^ k) β‖ ≤ ‖T ^ k‖ * ‖β‖ := (T ^ k).le_opNorm β
      _ ≤ ‖T‖ ^ k * ‖β‖ := mul_le_mul_of_nonneg_right (norm_pow_le' T hk) (norm_nonneg _)

omit [CompleteSpace X] in
/-- **The termwise bound.**  Each term is a geometric power of `‖T‖/2L` against `L^{-a}`. -/
theorem norm_resolventVecTerm_le {T : X →L[ℂ] X} {a L : ℝ} {g : ℕ → ℝ} (β : X) (hL : 0 < L)
    (k : ℕ) :
    ‖resolventCoeffG a g k L • (T ^ k) β‖
      ≤ (|g k| * (‖T‖ / (2 * L)) ^ k * ‖β‖) * L ^ (-a) := by
  have hcnn : 0 ≤ normalizedCentralBinom k := normalizedCentralBinom_nonneg k
  have hcle : normalizedCentralBinom k ≤ 1 := normalizedCentralBinom_le_one k
  have hsplit : L ^ (-((k : ℝ) + a)) = L ^ (-(k : ℝ)) * L ^ (-a) := by
    rw [← Real.rpow_add hL]
    congr 1
    ring
  have habs : |resolventCoeffG a g k L|
      = normalizedCentralBinom k * ((1 / 2 : ℝ) ^ k * L ^ (-(k : ℝ))) * |g k| * L ^ (-a) := by
    rw [resolventCoeffG, hsplit, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg hcnn, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k),
      abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hL.le _) (Real.rpow_nonneg hL.le _))]
    ring
  have hgeom : (1 / 2 : ℝ) ^ k * L ^ (-(k : ℝ)) * ‖T‖ ^ k = (‖T‖ / (2 * L)) ^ k := by
    rw [rpow_neg_natCast hL k, ← mul_pow, ← mul_pow]
    congr 1
    field_simp
  have hnn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k * L ^ (-(k : ℝ)) := by
    have := Real.rpow_nonneg hL.le (-(k : ℝ))
    positivity
  have hcoeff : |resolventCoeffG a g k L|
      ≤ ((1 / 2 : ℝ) ^ k * L ^ (-(k : ℝ))) * |g k| * L ^ (-a) := by
    rw [habs]
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
      (Real.rpow_nonneg hL.le _)
    calc normalizedCentralBinom k * ((1 / 2 : ℝ) ^ k * L ^ (-(k : ℝ)))
        ≤ 1 * ((1 / 2 : ℝ) ^ k * L ^ (-(k : ℝ))) := mul_le_mul_of_nonneg_right hcle hnn
      _ = (1 / 2 : ℝ) ^ k * L ^ (-(k : ℝ)) := one_mul _
  calc ‖resolventCoeffG a g k L • (T ^ k) β‖
      = |resolventCoeffG a g k L| * ‖(T ^ k) β‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ (((1 / 2 : ℝ) ^ k * L ^ (-(k : ℝ))) * |g k| * L ^ (-a)) * (‖T‖ ^ k * ‖β‖) :=
        mul_le_mul hcoeff (norm_pow_apply_le T β k) (norm_nonneg _) (by
          have := Real.rpow_nonneg hL.le (-a)
          positivity)
    _ = (|g k| * ((1 / 2 : ℝ) ^ k * L ^ (-(k : ℝ)) * ‖T‖ ^ k) * ‖β‖) * L ^ (-a) := by ring
    _ = (|g k| * (‖T‖ / (2 * L)) ^ k * ‖β‖) * L ^ (-a) := by rw [hgeom]

theorem summable_resolventVecTerm {T : X →L[ℂ] X} {a L : ℝ} {g : ℕ → ℝ} (β : X) (hL : 0 < L)
    (hg : Summable fun k : ℕ => |g k| * (‖T‖ / (2 * L)) ^ k) :
    Summable fun k : ℕ => resolventCoeffG a g k L • (T ^ k) β :=
  Summable.of_norm_bounded ((hg.mul_right ‖β‖).mul_right (L ^ (-a)))
    (fun k => by
      refine (norm_resolventVecTerm_le β hL k).trans (le_of_eq ?_)
      ring)

/-! ## The projection deletes grade zero and no path -/

/-- **The projected profile starts at grade one.**  A projection annihilating the trace deletes the
constant term of the expansion and nothing else: every adjacency word survives. -/
theorem proj_resolventVecProfile_eq_tail {T P : X →L[ℂ] X} {a L : ℝ} {g : ℕ → ℝ} {β : X}
    (hL : 0 < L) (hβ : P β = 0)
    (hg : Summable fun k : ℕ => |g k| * (‖T‖ / (2 * L)) ^ k) :
    P (resolventVecProfile T a g L β)
      = ∑' k : ℕ, resolventCoeffG a g (k + 1) L • P ((T ^ (k + 1)) β) := by
  have hsum := summable_resolventVecTerm (T := T) (a := a) (g := g) β hL hg
  have hmap : P (resolventVecProfile T a g L β)
      = ∑' k : ℕ, resolventCoeffG a g k L • P ((T ^ k) β) := by
    rw [resolventVecProfile, ← hsum.hasSum.mapL P |>.tsum_eq]
    exact tsum_congr fun k => by rw [ContinuousLinearMap.map_smul_of_tower]
  have hsumP : Summable fun k : ℕ => resolventCoeffG a g k L • P ((T ^ k) β) :=
    (hsum.hasSum.mapL P).summable.congr fun k => by
      rw [ContinuousLinearMap.map_smul_of_tower]
  rw [hmap, hsumP.tsum_eq_zero_add]
  simp [hβ]

/-! ## The grade-one rate -/

/-- **The grade-one decay rate.**  Once the trace is annihilated, the value profile decays one full
power faster than the unprojected one. -/
theorem norm_proj_resolventVecProfile_le {T P : X →L[ℂ] X} {L : ℝ} {β : X}
    (hL : 0 < L) (hT : ‖T‖ ≤ L) (hβ : P β = 0) :
    ‖P (resolventVecProfile T (1 / 2) gradeZeroWeight L β)‖
      ≤ (‖P‖ * ‖T‖ * ‖β‖) * L ^ (-(3 / 2 : ℝ)) := by
  set ρ : ℝ := ‖T‖ / (2 * L) with hρdef
  have hρ0 : 0 ≤ ρ := by positivity
  have hρhalf : ρ ≤ 1 / 2 := by
    rw [hρdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith [norm_nonneg T]
  have hρ1 : ρ < 1 := by linarith
  have hg : Summable fun k : ℕ => |gradeZeroWeight k| * ρ ^ k :=
    summable_of_le_polyGeom hρ0 hρ1 gradeZeroWeight_bound
  have hgP : Summable fun k : ℕ => |gradeZeroWeight k| * (‖T‖ / (2 * L)) ^ k := hg
  rw [proj_resolventVecProfile_eq_tail hL hβ hgP]
  -- termwise bound for the shifted series
  have hterm : ∀ k : ℕ,
      ‖resolventCoeffG (1 / 2) gradeZeroWeight (k + 1) L • P ((T ^ (k + 1)) β)‖
        ≤ (‖P‖ * ‖β‖ * L ^ (-(1 / 2 : ℝ))) * ρ ^ (k + 1) := by
    intro k
    have hbase := norm_resolventVecTerm_le (T := T) (a := 1 / 2) (g := gradeZeroWeight)
      β hL (k + 1)
    have hstep : ‖resolventCoeffG (1 / 2) gradeZeroWeight (k + 1) L • P ((T ^ (k + 1)) β)‖
        ≤ ‖P‖ * ‖resolventCoeffG (1 / 2) gradeZeroWeight (k + 1) L • (T ^ (k + 1)) β‖ := by
      rw [← ContinuousLinearMap.map_smul_of_tower]
      exact P.le_opNorm _
    refine hstep.trans ?_
    refine (mul_le_mul_of_nonneg_left hbase (norm_nonneg _)).trans (le_of_eq ?_)
    rw [gradeZeroWeight, abs_one]
    ring
  have hmaj : Summable fun k : ℕ => (‖P‖ * ‖β‖ * L ^ (-(1 / 2 : ℝ))) * ρ ^ (k + 1) := by
    refine ((summable_geometric_of_lt_one hρ0 hρ1).mul_left ρ).mul_left
      (‖P‖ * ‖β‖ * L ^ (-(1 / 2 : ℝ))) |>.congr fun k => ?_
    rw [pow_succ]
    ring
  have hnormsum : Summable fun k : ℕ =>
      ‖resolventCoeffG (1 / 2) gradeZeroWeight (k + 1) L • P ((T ^ (k + 1)) β)‖ :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hterm hmaj
  have hval : (∑' k : ℕ, (‖P‖ * ‖β‖ * L ^ (-(1 / 2 : ℝ))) * ρ ^ (k + 1))
      = (‖P‖ * ‖β‖ * L ^ (-(1 / 2 : ℝ))) * (ρ / (1 - ρ)) := by
    have hcongr : (fun k : ℕ => (‖P‖ * ‖β‖ * L ^ (-(1 / 2 : ℝ))) * ρ ^ (k + 1))
        = fun k : ℕ => ((‖P‖ * ‖β‖ * L ^ (-(1 / 2 : ℝ))) * ρ) * ρ ^ k := by
      funext k
      rw [pow_succ]
      ring
    rw [hcongr, tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ1]
    field_simp
  have hgeobound : ρ / (1 - ρ) ≤ ‖T‖ / L := by
    have hpos : (0 : ℝ) < 1 - ρ := by linarith
    have h2 : ρ / (1 - ρ) ≤ 2 * ρ := by
      rw [div_le_iff₀ hpos]
      nlinarith [hρ0, hρhalf]
    have h3 : 2 * ρ = ‖T‖ / L := by
      rw [hρdef]
      field_simp
    exact h3 ▸ h2
  have hexp : L ^ (-(1 / 2 : ℝ)) * (‖T‖ / L) = ‖T‖ * L ^ (-(3 / 2 : ℝ)) := by
    have hLne : L ≠ 0 := ne_of_gt hL
    rw [show (-(3 / 2 : ℝ)) = (-(1 / 2 : ℝ)) + (-1 : ℝ) by ring, Real.rpow_add hL,
      Real.rpow_neg_one]
    field_simp
  calc ‖∑' k : ℕ, resolventCoeffG (1 / 2) gradeZeroWeight (k + 1) L • P ((T ^ (k + 1)) β)‖
      ≤ ∑' k : ℕ, ‖resolventCoeffG (1 / 2) gradeZeroWeight (k + 1) L • P ((T ^ (k + 1)) β)‖ :=
        norm_tsum_le_tsum_norm hnormsum
    _ ≤ ∑' k : ℕ, (‖P‖ * ‖β‖ * L ^ (-(1 / 2 : ℝ))) * ρ ^ (k + 1) :=
        Summable.tsum_mono hnormsum hmaj hterm
    _ = (‖P‖ * ‖β‖ * L ^ (-(1 / 2 : ℝ))) * (ρ / (1 - ρ)) := hval
    _ ≤ (‖P‖ * ‖β‖ * L ^ (-(1 / 2 : ℝ))) * (‖T‖ / L) := by
        refine mul_le_mul_of_nonneg_left hgeobound ?_
        have := Real.rpow_nonneg hL.le (-(1 / 2 : ℝ))
        positivity
    _ = (‖P‖ * ‖T‖ * ‖β‖) * L ^ (-(3 / 2 : ℝ)) := by
        rw [mul_assoc, hexp]
        ring

end GaloisForLFunctions.HTGeometry
