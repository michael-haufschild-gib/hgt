import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenAdjacentSchedule

/-!
# Aligned cells for the Harman pair and triple terms

Aligned integer endpoints turn every active prime block into an exact interval `(Q,U]`.  Distinct
ordered cells make the prime-order conditions automatic.  The only excluded tuples are same-cell
order collisions and cells whose lower product is below the Harman threshold while their upper
product crosses it.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Real lower scale attached to the natural half-open block `[endpoint i,endpoint(i+1))`. -/
def mtAdjacentBlockLowerScale (endpoint : ℕ → ℕ) (i : ℕ) : ℝ :=
  ((endpoint i - 1 : ℕ) : ℝ)

/-- Real upper scale attached to the same block. -/
def mtAdjacentBlockUpperScale (endpoint : ℕ → ℕ) (i : ℕ) : ℝ :=
  ((endpoint (i + 1) - 1 : ℕ) : ℝ)

/-- Exact `(Q,U]` interpretation of one adjacent natural prime block. -/
theorem mem_mtAdjacentPrimeBlock_scale_iff
    {t : ℕ} {endpoint : ℕ → ℕ} (hendpoint : ∀ i, 1 ≤ endpoint i)
    (i : Fin t) (q : ℕ) :
    q ∈ mtAdjacentPrimeBlock endpoint i ↔
      q.Prime ∧ mtAdjacentBlockLowerScale endpoint i < (q : ℝ) ∧
        (q : ℝ) ≤ mtAdjacentBlockUpperScale endpoint i := by
  rw [mtAdjacentPrimeBlock, mem_primesIco]
  constructor
  · rintro ⟨hlower, hupper, hprime⟩
    refine ⟨hprime, ?_, ?_⟩
    · have : endpoint i.1 - 1 < q := by
        have := hendpoint i.1
        omega
      have hreal : ((endpoint i.1 - 1 : ℕ) : ℝ) < (q : ℝ) := by
        exact_mod_cast this
      simpa [mtAdjacentBlockLowerScale] using hreal
    · have : q ≤ endpoint (i.1 + 1) - 1 := by
        have := hendpoint (i.1 + 1)
        omega
      have hreal : (q : ℝ) ≤ ((endpoint (i.1 + 1) - 1 : ℕ) : ℝ) := by
        exact_mod_cast this
      simpa [mtAdjacentBlockUpperScale] using hreal
  · rintro ⟨hprime, hlower, hupper⟩
    have hlowerReal : ((endpoint i.1 - 1 : ℕ) : ℝ) < (q : ℝ) := by
      simpa [mtAdjacentBlockLowerScale] using hlower
    have hupperReal : (q : ℝ) ≤ ((endpoint (i.1 + 1) - 1 : ℕ) : ℝ) := by
      simpa [mtAdjacentBlockUpperScale] using hupper
    have hlowerNat : endpoint i.1 - 1 < q := by exact_mod_cast hlowerReal
    have hupperNat : q ≤ endpoint (i.1 + 1) - 1 := by exact_mod_cast hupperReal
    have hlowerPos := hendpoint i.1
    have hupperPos := hendpoint (i.1 + 1)
    exact ⟨by omega, by omega, hprime⟩

/-- If `q₂<q₁`, their block indices are ordered unless both primes occupy one collision block. -/
theorem adjacentBlock_eq_or_lt_of_prime_lt
    {t : ℕ} {endpoint : ℕ → ℕ} (hmono : Monotone endpoint)
    {i₁ i₂ : Fin t} {q₁ q₂ : ℕ}
    (hq₁ : q₁ ∈ mtAdjacentPrimeBlock endpoint i₁)
    (hq₂ : q₂ ∈ mtAdjacentPrimeBlock endpoint i₂)
    (hlt : q₂ < q₁) :
    i₂ = i₁ ∨ i₂.1 < i₁.1 := by
  have hnot : ¬i₁.1 < i₂.1 := by
    intro hi
    have hq₁Upper := (mem_primesIco.mp hq₁).2.1
    have hq₂Lower := (mem_primesIco.mp hq₂).1
    have hendpointLe : endpoint (i₁.1 + 1) ≤ endpoint i₂.1 := hmono (by omega)
    omega
  rcases eq_or_lt_of_le (Nat.le_of_not_gt hnot) with heq | hltIdx
  · exact Or.inl (Fin.ext heq)
  · exact Or.inr hltIdx

/-- Strictly ordered adjacent block indices make the corresponding prime order automatic. -/
theorem prime_lt_of_adjacentBlock_index_lt
    {t : ℕ} {endpoint : ℕ → ℕ} (hmono : Monotone endpoint)
    {i₁ i₂ : Fin t} {q₁ q₂ : ℕ}
    (hidx : i₂.1 < i₁.1)
    (hq₁ : q₁ ∈ mtAdjacentPrimeBlock endpoint i₁)
    (hq₂ : q₂ ∈ mtAdjacentPrimeBlock endpoint i₂) :
    q₂ < q₁ := by
  have hq₁Lower := (mem_primesIco.mp hq₁).1
  have hq₂Upper := (mem_primesIco.mp hq₂).2.1
  have hendpointLe : endpoint (i₂.1 + 1) ≤ endpoint i₁.1 := hmono (by omega)
  omega

/-- Lower block scales lie strictly below the actual Harman pair product. -/
theorem adjacentBlock_lower_product_lt
    {t : ℕ} {endpoint : ℕ → ℕ} (hendpoint : ∀ i, 1 ≤ endpoint i)
    {i₁ i₂ : Fin t} {q₁ q₂ : ℕ}
    (hq₁ : q₁ ∈ mtAdjacentPrimeBlock endpoint i₁)
    (hq₂ : q₂ ∈ mtAdjacentPrimeBlock endpoint i₂) :
    mtAdjacentBlockLowerScale endpoint i₁ *
        mtAdjacentBlockLowerScale endpoint i₂ ^ (4 : ℕ) <
      (q₁ : ℝ) * (q₂ : ℝ) ^ (4 : ℕ) := by
  have h₁ := (mem_mtAdjacentPrimeBlock_scale_iff hendpoint i₁ q₁).mp hq₁ |>.2.1
  have h₂ := (mem_mtAdjacentPrimeBlock_scale_iff hendpoint i₂ q₂).mp hq₂ |>.2.1
  have hlower₂_nonneg : 0 ≤ mtAdjacentBlockLowerScale endpoint i₂ := by
    simp [mtAdjacentBlockLowerScale]
  have hq₁pos : 0 < (q₁ : ℝ) :=
    lt_of_le_of_lt (by simp [mtAdjacentBlockLowerScale]) h₁
  have h₂pow : mtAdjacentBlockLowerScale endpoint i₂ ^ (4 : ℕ) < (q₂ : ℝ) ^ (4 : ℕ) :=
    pow_lt_pow_left₀ h₂ hlower₂_nonneg (by norm_num)
  calc
    mtAdjacentBlockLowerScale endpoint i₁ *
        mtAdjacentBlockLowerScale endpoint i₂ ^ (4 : ℕ) ≤
      (q₁ : ℝ) * mtAdjacentBlockLowerScale endpoint i₂ ^ (4 : ℕ) :=
        mul_le_mul_of_nonneg_right h₁.le (by positivity)
    _ < (q₁ : ℝ) * (q₂ : ℝ) ^ (4 : ℕ) :=
      mul_lt_mul_of_pos_left h₂pow hq₁pos

/-- Actual prime product is at most the product of its block upper scales. -/
theorem adjacentBlock_product_le_upper
    {t : ℕ} {endpoint : ℕ → ℕ} (hendpoint : ∀ i, 1 ≤ endpoint i)
    {i₁ i₂ : Fin t} {q₁ q₂ : ℕ}
    (hq₁ : q₁ ∈ mtAdjacentPrimeBlock endpoint i₁)
    (hq₂ : q₂ ∈ mtAdjacentPrimeBlock endpoint i₂) :
    (q₁ : ℝ) * (q₂ : ℝ) ^ (4 : ℕ) ≤
      mtAdjacentBlockUpperScale endpoint i₁ *
        mtAdjacentBlockUpperScale endpoint i₂ ^ (4 : ℕ) := by
  have h₁ := (mem_mtAdjacentPrimeBlock_scale_iff hendpoint i₁ q₁).mp hq₁ |>.2.2
  have h₂ := (mem_mtAdjacentPrimeBlock_scale_iff hendpoint i₂ q₂).mp hq₂ |>.2.2
  have hupper₁_nonneg : 0 ≤ mtAdjacentBlockUpperScale endpoint i₁ := by
    simp [mtAdjacentBlockUpperScale]
  have h₂pow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ q₂) h₂ 4
  calc
    (q₁ : ℝ) * (q₂ : ℝ) ^ (4 : ℕ) ≤
        mtAdjacentBlockUpperScale endpoint i₁ * (q₂ : ℝ) ^ (4 : ℕ) :=
      mul_le_mul_of_nonneg_right h₁ (by positivity)
    _ ≤ mtAdjacentBlockUpperScale endpoint i₁ *
        mtAdjacentBlockUpperScale endpoint i₂ ^ (4 : ℕ) :=
      mul_le_mul_of_nonneg_left h₂pow hupper₁_nonneg

/-- One cell upper-product is strictly below the fifth power of its block-width dilation times
the actual Harman pair product. -/
theorem adjacentBlock_upper_product_lt_dilated_actual
    {t : ℕ} {endpoint : ℕ → ℕ} (hendpoint : ∀ i, 1 ≤ endpoint i)
    {i₁ i₂ : Fin t} {q₁ q₂ : ℕ} {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hband : ∀ i : Fin t,
      mtAdjacentBlockUpperScale endpoint i ≤
        (1 + δ) * mtAdjacentBlockLowerScale endpoint i)
    (hq₁ : q₁ ∈ mtAdjacentPrimeBlock endpoint i₁)
    (hq₂ : q₂ ∈ mtAdjacentPrimeBlock endpoint i₂) :
    mtAdjacentBlockUpperScale endpoint i₁ *
        mtAdjacentBlockUpperScale endpoint i₂ ^ (4 : ℕ) <
      (1 + δ) ^ (5 : ℕ) * ((q₁ : ℝ) * (q₂ : ℝ) ^ (4 : ℕ)) := by
  have hq₁Mem := (mem_mtAdjacentPrimeBlock_scale_iff hendpoint i₁ q₁).mp hq₁
  have hq₂Mem := (mem_mtAdjacentPrimeBlock_scale_iff hendpoint i₂ q₂).mp hq₂
  have hdilation : 0 < 1 + δ := by linarith
  have hupper₁ : mtAdjacentBlockUpperScale endpoint i₁ < (1 + δ) * (q₁ : ℝ) :=
    (hband i₁).trans_lt (mul_lt_mul_of_pos_left hq₁Mem.2.1 hdilation)
  have hupper₂ : mtAdjacentBlockUpperScale endpoint i₂ < (1 + δ) * (q₂ : ℝ) :=
    (hband i₂).trans_lt (mul_lt_mul_of_pos_left hq₂Mem.2.1 hdilation)
  have hq₁Pos : 0 < (q₁ : ℝ) := by exact_mod_cast hq₁Mem.1.pos
  have hq₂Pos : 0 < (q₂ : ℝ) := by exact_mod_cast hq₂Mem.1.pos
  have hupper₂Pos : 0 < mtAdjacentBlockUpperScale endpoint i₂ :=
    hq₂Pos.trans_le hq₂Mem.2.2
  have hupper₂Pow : mtAdjacentBlockUpperScale endpoint i₂ ^ (4 : ℕ) <
      ((1 + δ) * (q₂ : ℝ)) ^ (4 : ℕ) :=
    pow_lt_pow_left₀ hupper₂ hupper₂Pos.le (by norm_num)
  calc
    mtAdjacentBlockUpperScale endpoint i₁ *
        mtAdjacentBlockUpperScale endpoint i₂ ^ (4 : ℕ) <
      ((1 + δ) * (q₁ : ℝ)) * mtAdjacentBlockUpperScale endpoint i₂ ^ (4 : ℕ) :=
        mul_lt_mul_of_pos_right hupper₁ (pow_pos hupper₂Pos 4)
    _ < ((1 + δ) * (q₁ : ℝ)) * ((1 + δ) * (q₂ : ℝ)) ^ (4 : ℕ) :=
      mul_lt_mul_of_pos_left hupper₂Pow (mul_pos hdilation hq₁Pos)
    _ = (1 + δ) ^ (5 : ℕ) * ((q₁ : ℝ) * (q₂ : ℝ) ^ (4 : ℕ)) := by ring

/-- A threshold-crossing cell places its actual pair in a multiplicative window of exact relative
width `(1+δ)^(5 : ℕ)`. -/
theorem adjacentBlock_thresholdBoundary_implies_harmanWindow
    {t : ℕ} {endpoint : ℕ → ℕ} (hendpoint : ∀ i, 1 ≤ endpoint i)
    {i₁ i₂ : Fin t} {q₁ q₂ : ℕ} {δ E : ℝ}
    (hδ : 0 ≤ δ)
    (hband : ∀ i : Fin t,
      mtAdjacentBlockUpperScale endpoint i ≤
        (1 + δ) * mtAdjacentBlockLowerScale endpoint i)
    (hq₁ : q₁ ∈ mtAdjacentPrimeBlock endpoint i₁)
    (hq₂ : q₂ ∈ mtAdjacentPrimeBlock endpoint i₂)
    (hgeometry : (q₁ : ℝ) * (q₂ : ℝ) ^ (4 : ℕ) < E)
    (hboundary : E ≤ mtAdjacentBlockUpperScale endpoint i₁ *
      mtAdjacentBlockUpperScale endpoint i₂ ^ (4 : ℕ)) :
    E < (1 + δ) ^ (5 : ℕ) * ((q₁ : ℝ) * (q₂ : ℝ) ^ (4 : ℕ)) ∧
      (q₁ : ℝ) * (q₂ : ℝ) ^ (4 : ℕ) < E := by
  exact ⟨hboundary.trans_lt
    (adjacentBlock_upper_product_lt_dilated_actual
      hendpoint hδ hband hq₁ hq₂), hgeometry⟩

/-- Every admissible Harman pair cell is either uniformly good or an explicit threshold-crossing
boundary cell. -/
theorem adjacentBlock_good_or_thresholdBoundary
    {t : ℕ} {endpoint : ℕ → ℕ} (hendpoint : ∀ i, 1 ≤ endpoint i)
    {i₁ i₂ : Fin t} {q₁ q₂ : ℕ} {E : ℝ}
    (hq₁ : q₁ ∈ mtAdjacentPrimeBlock endpoint i₁)
    (hq₂ : q₂ ∈ mtAdjacentPrimeBlock endpoint i₂)
    (hgeometry : (q₁ : ℝ) * (q₂ : ℝ) ^ (4 : ℕ) < E) :
    mtAdjacentBlockUpperScale endpoint i₁ *
        mtAdjacentBlockUpperScale endpoint i₂ ^ (4 : ℕ) < E ∨
      (mtAdjacentBlockLowerScale endpoint i₁ *
          mtAdjacentBlockLowerScale endpoint i₂ ^ (4 : ℕ) < E ∧
        E ≤ mtAdjacentBlockUpperScale endpoint i₁ *
          mtAdjacentBlockUpperScale endpoint i₂ ^ (4 : ℕ)) := by
  by_cases hgood : mtAdjacentBlockUpperScale endpoint i₁ *
      mtAdjacentBlockUpperScale endpoint i₂ ^ (4 : ℕ) < E
  · exact Or.inl hgood
  · exact Or.inr ⟨(adjacentBlock_lower_product_lt hendpoint hq₁ hq₂).trans hgeometry,
      le_of_not_gt hgood⟩

end

end RHTower.Sieve
