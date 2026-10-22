import GaloisForLFunctions.RHTower.Deninger.DeningerPeriodCutoff
import GaloisForLFunctions.RHTower.Deninger.DeningerSmoothPeriodic

/-!
# The periodization lands in the smooth periodic test space

Cutting the lattice sum down to a neighbourhood of one period produces a series with a summable
majorant of every derivative order, hence a smooth sum.  On the inner interval the cutoff is `1`,
so the periodization agrees there with that smooth function and is smooth on a neighbourhood of one
period; periodicity then propagates smoothness to the whole line.

* `deningerCutoffTerm` : the cut lattice term `\chi(t)h(t+jL)`.
* `deningerCutoffSum_contDiff` : **the cut lattice sum is smooth.**
* `deningerPeriodizationSum_contDiff` : **`Per_L h` is smooth.**
* `deningerPeriodizationMem` : **`Per_L h` lies in `C^\infty(\mathbb R/L\mathbb Z)`.**
-/

namespace RHTower

open SchwartzMap Metric

noncomputable section

/-- The lattice term cut down to a neighbourhood of one period. -/
def deningerCutoffTerm (L : ℝ) (f : 𝓢(ℝ, ℂ)) (j : ℤ) : ℝ → ℂ :=
  fun t => (deningerPeriodCutoff L : ℝ → ℝ) t • (f : ℝ → ℂ) (t + (j : ℝ) * L)

theorem deningerCutoffTerm_contDiff (L : ℝ) (f : 𝓢(ℝ, ℂ)) (j : ℤ) :
    ContDiff ℝ (⊤ : ℕ∞) (deningerCutoffTerm L f j) := by
  refine (deningerPeriodCutoff_contDiff L).smul ?_
  exact (f.smooth (⊤ : ℕ∞)).comp (contDiff_id.add contDiff_const)

/-- **Every derivative of the cut lattice term has a geometric bound in the lattice index.** -/
theorem deningerCutoffTerm_iteratedFDeriv_bound {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerExpSchwartz)
    {L : ℝ} (hL : 0 < L) (k : ℕ) :
    ∃ V : ℝ, 0 ≤ V ∧ ∀ (j : ℤ) (t : ℝ),
      ‖iteratedFDeriv ℝ k (deningerCutoffTerm L f j) t‖
        ≤ V * (Real.exp (-L)) ^ j.natAbs := by
  obtain ⟨D, hDnn, hD⟩ := deningerPeriodCutoff_iteratedFDeriv_bound L k
  have hC : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ,
      ‖iteratedFDeriv ℝ m (f : ℝ → ℂ) x‖ ≤ C * Real.exp (-|x|) := by
    intro m
    obtain ⟨C, hCle⟩ := hf 1 m
    refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
    have hx := hCle x
    rw [one_mul] at hx
    have hpos : (0 : ℝ) < Real.exp |x| := Real.exp_pos _
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hpos]
    calc ‖iteratedFDeriv ℝ m (f : ℝ → ℂ) x‖ * Real.exp |x|
        = Real.exp |x| * ‖iteratedFDeriv ℝ m (f : ℝ → ℂ) x‖ := by ring
      _ ≤ max C 0 := le_trans hx (le_max_left _ _)
  choose C hCnn hCle using hC
  set Ck : ℝ := ∑ m ∈ Finset.range (k + 1), C m with hCk
  have hCknn : 0 ≤ Ck := Finset.sum_nonneg fun m _ => hCnn m
  have hCkle : ∀ m ≤ k, ∀ x : ℝ,
      ‖iteratedFDeriv ℝ m (f : ℝ → ℂ) x‖ ≤ Ck * Real.exp (-|x|) := by
    intro m hm x
    refine le_trans (hCle m x) (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
    exact Finset.single_le_sum (f := C) (fun i _ => hCnn i)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hm))
  refine ⟨2 ^ k * D * Ck * Real.exp (|L| + 5), by positivity, fun j t => ?_⟩
  -- The Leibniz bound for the product.
  have hleib : ‖iteratedFDeriv ℝ k (deningerCutoffTerm L f j) t‖
      ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)
          * ‖iteratedFDeriv ℝ i (deningerPeriodCutoff L : ℝ → ℝ) t‖
          * ‖iteratedFDeriv ℝ (k - i) (fun s : ℝ => (f : ℝ → ℂ) (s + (j : ℝ) * L)) t‖ :=
    norm_iteratedFDeriv_smul_le (deningerPeriodCutoff_contDiff L)
      ((f.smooth (⊤ : ℕ∞)).comp (contDiff_id.add contDiff_const)) t (by exact_mod_cast le_top)
  refine le_trans hleib ?_
  by_cases hin : |t| ≤ |L| + 5
  · -- On the support the translate is far from the origin.
    have hfar : ∀ m : ℕ, m ≤ k →
        ‖iteratedFDeriv ℝ m (fun s : ℝ => (f : ℝ → ℂ) (s + (j : ℝ) * L)) t‖
          ≤ Ck * Real.exp (|L| + 5) * (Real.exp (-L)) ^ j.natAbs := by
      intro m hm
      rw [iteratedFDeriv_comp_add_right]
      refine le_trans (hCkle m hm (t + (j : ℝ) * L)) ?_
      have hdist : (j.natAbs : ℝ) * L - (|L| + 5) ≤ |t + (j : ℝ) * L| := by
        have h1 : |(j : ℝ) * L| = (j.natAbs : ℝ) * L := by
          rw [abs_mul, abs_of_pos hL, ← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
        have h2 : |(j : ℝ) * L| - |t| ≤ |t + (j : ℝ) * L| := by
          have := abs_sub_abs_le_abs_sub ((j : ℝ) * L) (-t)
          simp only [sub_neg_eq_add, abs_neg] at this
          calc |(j : ℝ) * L| - |t| ≤ |(j : ℝ) * L + t| := this
            _ = |t + (j : ℝ) * L| := by rw [add_comm]
        rw [← h1]
        linarith
      have hexp : Real.exp (-|t + (j : ℝ) * L|)
          ≤ Real.exp (|L| + 5) * (Real.exp (-L)) ^ j.natAbs := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        have : (j.natAbs : ℝ) * (-L) = -((j.natAbs : ℝ) * L) := by ring
        rw [this]
        linarith
      calc Ck * Real.exp (-|t + (j : ℝ) * L|)
          ≤ Ck * (Real.exp (|L| + 5) * (Real.exp (-L)) ^ j.natAbs) :=
            mul_le_mul_of_nonneg_left hexp hCknn
        _ = Ck * Real.exp (|L| + 5) * (Real.exp (-L)) ^ j.natAbs := by ring
    calc ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)
            * ‖iteratedFDeriv ℝ i (deningerPeriodCutoff L : ℝ → ℝ) t‖
            * ‖iteratedFDeriv ℝ (k - i) (fun s : ℝ => (f : ℝ → ℂ) (s + (j : ℝ) * L)) t‖
        ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)
            * D * (Ck * Real.exp (|L| + 5) * (Real.exp (-L)) ^ j.natAbs) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
          refine mul_le_mul (mul_le_mul_of_nonneg_left (hD i hik t) (by positivity))
            (hfar (k - i) (Nat.sub_le _ _)) (norm_nonneg _) (by positivity)
      _ = 2 ^ k * D * Ck * Real.exp (|L| + 5) * (Real.exp (-L)) ^ j.natAbs := by
          have hsum : (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) = 2 ^ k := by
            rw [← Nat.cast_sum, Nat.sum_range_choose]
            push_cast
            ring
          rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]
          ring
  · -- Off the support every term vanishes.
    have hzero : ∀ i ∈ Finset.range (k + 1), (k.choose i : ℝ)
        * ‖iteratedFDeriv ℝ i (deningerPeriodCutoff L : ℝ → ℝ) t‖
        * ‖iteratedFDeriv ℝ (k - i) (fun s : ℝ => (f : ℝ → ℂ) (s + (j : ℝ) * L)) t‖ = 0 := by
      intro i _
      rw [deningerPeriodCutoff_iteratedFDeriv_eq_zero (not_le.1 hin) i]
      simp
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero]
    positivity

/-- **The cut lattice sum is smooth.** -/
theorem deningerCutoffSum_contDiff {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerExpSchwartz) {L : ℝ}
    (hL : 0 < L) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t => ∑' j : ℤ, deningerCutoffTerm L f j t) := by
  choose V hVnn hVle using fun k => deningerCutoffTerm_iteratedFDeriv_bound hf hL k
  refine contDiff_tsum (v := fun k j => V k * (Real.exp (-L)) ^ j.natAbs)
    (fun j => deningerCutoffTerm_contDiff L f j) (fun k _ => ?_) (fun k j t _ => hVle k j t)
  exact deningerGeometricInt_summable (C := V k) hL

/-- On the inner interval the cut sum is the periodization. -/
theorem deningerCutoffSum_eq_periodization (L : ℝ) (f : 𝓢(ℝ, ℂ)) {t : ℝ}
    (ht : |t| ≤ |L| + 4) :
    (∑' j : ℤ, deningerCutoffTerm L f j t) = deningerPeriodizationSum f L t := by
  rw [deningerPeriodizationSum]
  refine tsum_congr fun j => ?_
  rw [deningerCutoffTerm, deningerPeriodCutoff_eq_one ht, one_smul]

/-- **The periodization is smooth.** -/
theorem deningerPeriodizationSum_contDiff {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerExpSchwartz) {L : ℝ}
    (hL : 0 < L) : ContDiff ℝ (⊤ : ℕ∞) (deningerPeriodizationSum f L) := by
  have hper : Function.Periodic (deningerPeriodizationSum f L) L :=
    fun t => deningerPeriodizationSum_periodic f L t
  -- Smoothness near one period, from the cut sum.
  have hnear : ∀ t : ℝ, |t| < |L| + 4 → ContDiffAt ℝ (⊤ : ℕ∞) (deningerPeriodizationSum f L) t := by
    intro t ht
    refine ((deningerCutoffSum_contDiff hf hL).contDiffAt).congr_of_eventuallyEq ?_
    have hball : Metric.ball (0 : ℝ) (|L| + 4) ∈ nhds t := by
      refine Metric.isOpen_ball.mem_nhds ?_
      simpa [Real.dist_eq] using ht
    refine Filter.eventuallyEq_of_mem hball fun s hs => ?_
    refine (deningerCutoffSum_eq_periodization L f ?_).symm
    have : |s| < |L| + 4 := by simpa [Real.dist_eq] using hs
    exact this.le
  -- Propagate by periodicity.
  rw [contDiff_iff_contDiffAt]
  intro t
  set n : ℤ := -⌊t / L⌋ with hn
  have hshift : |t + (n : ℝ) * L| < |L| + 4 := by
    have hfr : t + (n : ℝ) * L = L * Int.fract (t / L) := by
      rw [hn, Int.fract]
      push_cast
      field_simp
      ring
    have h0 : 0 ≤ Int.fract (t / L) := Int.fract_nonneg _
    have h1 : Int.fract (t / L) < 1 := Int.fract_lt_one _
    rw [hfr, abs_of_nonneg (by positivity)]
    have : L * Int.fract (t / L) < L := mul_lt_of_lt_one_right hL h1
    have hLabs : L ≤ |L| := le_abs_self L
    linarith
  have hat := hnear _ hshift
  have hcomp : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun s : ℝ => deningerPeriodizationSum f L (s + (n : ℝ) * L)) t :=
    hat.comp t (contDiff_id.add contDiff_const).contDiffAt
  refine hcomp.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  exact ((hper.int_mul n) s).symm

/-- **The periodization lies in the smooth periodic test space `C^∞(ℝ/Lℤ)`.** -/
theorem deningerPeriodizationMem {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerExpSchwartz) {L : ℝ}
    (hL : 0 < L) : deningerPeriodizationSum f L ∈ DeningerSmoothPeriodic L :=
  ⟨deningerPeriodizationSum_contDiff hf hL, fun t => deningerPeriodizationSum_periodic f L t⟩

end

end RHTower
