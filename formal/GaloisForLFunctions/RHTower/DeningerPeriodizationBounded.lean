import GaloisForLFunctions.RHTower.DeningerPeriodizationSplit
import GaloisForLFunctions.RHTower.DeningerMeyerSeminorm

/-!
# The periodization is bounded by the Meyer seminorms

On the interval where the cutoff is `1` the periodization and the cut sum have the same derivatives,
so every derivative of `Per_L h` is the periodized derivative of `h`.  The Meyer seminorm of order
`r` dominates each term geometrically, so the sup-norm of the `r`-th derivative of `Per_L h` is
bounded by a constant multiple of `q_{1,r}(h)`, uniformly in `t` by periodicity.

* `deningerPeriodizationSum_iteratedFDeriv` : **`(Per_L h)^{(r)} = Per_L(h^{(r)})` on one period.**
* `deningerPeriodizationSum_iteratedFDeriv_periodic` : the derivatives are `L`-periodic.
* `deningerPeriodizationSum_iteratedFDeriv_bound` : **`\sup_t \|(Per_L h)^{(r)}(t)\| \le K q_{1,r}(h)`.**
-/

namespace RHTower

open SchwartzMap Metric

noncomputable section

/-- The cut term agrees with the plain translate where the cutoff is `1`. -/
theorem deningerCutoffTerm_iteratedFDeriv_eq (L : ℝ) (f : 𝓢(ℝ, ℂ)) (j : ℤ) (r : ℕ) {t : ℝ}
    (ht : t ∈ ball (0 : ℝ) (|L| + 4)) :
    iteratedFDeriv ℝ r (deningerCutoffTerm L f j) t
      = iteratedFDeriv ℝ r (fun s : ℝ => (f : ℝ → ℂ) (s + (j : ℝ) * L)) t := by
  have hEq : Set.EqOn (deningerCutoffTerm L f j)
      (fun s : ℝ => (f : ℝ → ℂ) (s + (j : ℝ) * L)) (ball (0 : ℝ) (|L| + 4)) := by
    intro s hs
    have hs' : |s| ≤ |L| + 4 := le_of_lt (by simpa [Real.dist_eq] using hs)
    rw [deningerCutoffTerm, deningerPeriodCutoff_eq_one hs', one_smul]
  rw [← iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) r isOpen_ball ht,
    ← iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) r isOpen_ball ht,
    iteratedFDerivWithin_congr hEq ht]

set_option maxHeartbeats 1000000 in
/-- **On one period the derivatives of the periodization are the periodized derivatives.** -/
theorem deningerPeriodizationSum_iteratedFDeriv {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerExpSchwartz)
    {L : ℝ} (hL : 0 < L) (r : ℕ) {t : ℝ} (ht : t ∈ ball (0 : ℝ) (|L| + 4)) :
    iteratedFDeriv ℝ r (deningerPeriodizationSum f L) t
      = ∑' j : ℤ, iteratedFDeriv ℝ r (f : ℝ → ℂ) (t + (j : ℝ) * L) := by
  have hEq : Set.EqOn (deningerPeriodizationSum f L)
      (fun s => ∑' j : ℤ, deningerCutoffTerm L f j s) (ball (0 : ℝ) (|L| + 4)) := by
    intro s hs
    have hs' : |s| ≤ |L| + 4 := le_of_lt (by simpa [Real.dist_eq] using hs)
    exact (deningerCutoffSum_eq_periodization L f hs').symm
  rw [← iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) r isOpen_ball ht,
    iteratedFDerivWithin_congr hEq ht, iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) r isOpen_ball ht]
  choose V hVnn hVle using fun k => deningerCutoffTerm_iteratedFDeriv_bound hf hL k
  have hsm : ∀ k : ℕ, (k : ℕ∞) ≤ (⊤ : ℕ∞) →
      Summable (fun j : ℤ => V k * (Real.exp (-L)) ^ j.natAbs) :=
    fun k _ => deningerGeometricInt_summable (C := V k) hL
  have hbd : ∀ (k : ℕ) (i : ℤ) (x : ℝ), (k : ℕ∞) ≤ (⊤ : ℕ∞) →
      ‖iteratedFDeriv ℝ k (deningerCutoffTerm L f i) x‖
        ≤ V k * (Real.exp (-L)) ^ i.natAbs := fun k j x _ => hVle k j x
  have hkey := iteratedFDeriv_tsum_apply (𝕜 := ℝ) (N := (⊤ : ℕ∞))
    (v := fun k j => V k * (Real.exp (-L)) ^ j.natAbs)
    (fun j => deningerCutoffTerm_contDiff L f j) hsm hbd (k := r) le_top t
  rw [hkey]
  refine tsum_congr fun j => ?_
  rw [deningerCutoffTerm_iteratedFDeriv_eq L f j r ht, iteratedFDeriv_comp_add_right]

/-- The derivatives of the periodization are `L`-periodic. -/
theorem deningerPeriodizationSum_iteratedFDeriv_periodic (f : 𝓢(ℝ, ℂ)) (L : ℝ) (r : ℕ) (t : ℝ) :
    iteratedFDeriv ℝ r (deningerPeriodizationSum f L) (t + L)
      = iteratedFDeriv ℝ r (deningerPeriodizationSum f L) t := by
  have hfun : (fun s : ℝ => deningerPeriodizationSum f L (s + L))
      = deningerPeriodizationSum f L :=
    funext fun s => deningerPeriodizationSum_periodic f L s
  have h := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := deningerPeriodizationSum f L) r L t
  rw [hfun] at h
  exact h.symm

theorem deningerPeriodizationSum_iteratedFDeriv_int_shift (f : 𝓢(ℝ, ℂ)) (L : ℝ) (r : ℕ) (t : ℝ)
    (j : ℤ) :
    iteratedFDeriv ℝ r (deningerPeriodizationSum f L) (t + (j : ℝ) * L)
      = iteratedFDeriv ℝ r (deningerPeriodizationSum f L) t :=
  (Function.Periodic.int_mul
    (fun s => deningerPeriodizationSum_iteratedFDeriv_periodic f L r s) j) t

/-- **The periodization is bounded by the Meyer seminorms.**  Every derivative of `Per_L h` is
dominated by a fixed multiple of the Meyer seminorm of the same order, uniformly on the line. -/
theorem deningerPeriodizationSum_iteratedFDeriv_bound {L : ℝ} (hL : 0 < L) (r : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h : DeningerExpSchwartz, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ r (deningerPeriodizationSum ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) L) t‖
        ≤ K * deningerMeyerSeminormFun 1 r h := by
  have hgeo : Summable fun j : ℤ => (1 : ℝ) * (Real.exp (-L)) ^ j.natAbs :=
    deningerGeometricInt_summable (C := 1) hL
  refine ⟨Real.exp (|L|) * ∑' j : ℤ, (1 : ℝ) * (Real.exp (-L)) ^ j.natAbs, by positivity, ?_⟩
  intro h t
  set q : ℝ := deningerMeyerSeminormFun 1 r h with hq
  have hqnn : 0 ≤ q := deningerMeyerSeminormFun_nonneg 1 r h
  -- Pointwise decay from the Meyer seminorm.
  have hdec : ∀ x : ℝ,
      ‖iteratedFDeriv ℝ r (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖
        ≤ q * Real.exp (-|x|) := by
    intro x
    have hw := deningerMeyerWeight_le 1 r h x
    rw [deningerMeyerWeight, one_mul] at hw
    have hpos : (0 : ℝ) < Real.exp |x| := Real.exp_pos _
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hpos]
    calc ‖iteratedFDeriv ℝ r (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖ * Real.exp |x|
        = Real.exp |x| * ‖iteratedFDeriv ℝ r
            (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖ := by ring
      _ ≤ q := hw
  -- Reduce to one period.
  set n : ℤ := -⌊t / L⌋ with hn
  have hfr : t + (n : ℝ) * L = L * Int.fract (t / L) := by
    rw [hn, Int.fract]
    push_cast
    field_simp
    ring
  have hmem : t + (n : ℝ) * L ∈ ball (0 : ℝ) (|L| + 4) := by
    have h0 : 0 ≤ Int.fract (t / L) := Int.fract_nonneg _
    have h1 : Int.fract (t / L) < 1 := Int.fract_lt_one _
    have hlt : L * Int.fract (t / L) < L := mul_lt_of_lt_one_right hL h1
    have hLabs : L ≤ |L| := le_abs_self L
    have habs : |t + (n : ℝ) * L| < |L| + 4 := by
      rw [hfr, abs_of_nonneg (by positivity)]
      linarith
    simpa [Real.dist_eq] using habs
  rw [← deningerPeriodizationSum_iteratedFDeriv_int_shift _ L r t n,
    deningerPeriodizationSum_iteratedFDeriv h.2 hL r hmem]
  -- Bound the periodized derivative term by term.
  set u : ℝ := t + (n : ℝ) * L with hu
  have huabs : |u| ≤ |L| := by
    have h0 : 0 ≤ Int.fract (t / L) := Int.fract_nonneg _
    have h1 : Int.fract (t / L) < 1 := Int.fract_lt_one _
    have hlt : L * Int.fract (t / L) < L := mul_lt_of_lt_one_right hL h1
    have hLabs : L ≤ |L| := le_abs_self L
    rw [hfr, abs_of_nonneg (by positivity)]
    linarith
  have hterm : ∀ j : ℤ,
      ‖iteratedFDeriv ℝ r (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (u + (j : ℝ) * L)‖
        ≤ q * (Real.exp (|L|) * ((1 : ℝ) * (Real.exp (-L)) ^ j.natAbs)) := by
    intro j
    refine le_trans (hdec _) ?_
    have hdist : (j.natAbs : ℝ) * L - |L| ≤ |u + (j : ℝ) * L| := by
      have h1 : |(j : ℝ) * L| = (j.natAbs : ℝ) * L := by
        rw [abs_mul, abs_of_pos hL, ← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      have h2 : |(j : ℝ) * L| - |u| ≤ |u + (j : ℝ) * L| := by
        have hb := abs_sub_abs_le_abs_sub ((j : ℝ) * L) (-u)
        simp only [sub_neg_eq_add, abs_neg] at hb
        calc |(j : ℝ) * L| - |u| ≤ |(j : ℝ) * L + u| := hb
          _ = |u + (j : ℝ) * L| := by rw [add_comm]
      rw [← h1]
      linarith
    have hexp : Real.exp (-|u + (j : ℝ) * L|)
        ≤ Real.exp (|L|) * ((1 : ℝ) * (Real.exp (-L)) ^ j.natAbs) := by
      rw [one_mul, ← Real.exp_nat_mul, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have hrw : (j.natAbs : ℝ) * (-L) = -((j.natAbs : ℝ) * L) := by ring
      rw [hrw]
      linarith
    exact mul_le_mul_of_nonneg_left hexp hqnn
  have hsummable : Summable fun j : ℤ =>
      ‖iteratedFDeriv ℝ r (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (u + (j : ℝ) * L)‖ :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hterm
      ((hgeo.mul_left (Real.exp |L|)).mul_left q)
  calc ‖∑' j : ℤ, iteratedFDeriv ℝ r (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
          (u + (j : ℝ) * L)‖
      ≤ ∑' j : ℤ, ‖iteratedFDeriv ℝ r (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
          (u + (j : ℝ) * L)‖ := norm_tsum_le_tsum_norm hsummable
    _ ≤ ∑' j : ℤ, q * (Real.exp (|L|) * ((1 : ℝ) * (Real.exp (-L)) ^ j.natAbs)) :=
        hsummable.tsum_le_tsum hterm ((hgeo.mul_left (Real.exp |L|)).mul_left q)
    _ = (Real.exp (|L|) * ∑' j : ℤ, (1 : ℝ) * (Real.exp (-L)) ^ j.natAbs) * q := by
        rw [tsum_mul_left, tsum_mul_left]
        ring

end

end RHTower
