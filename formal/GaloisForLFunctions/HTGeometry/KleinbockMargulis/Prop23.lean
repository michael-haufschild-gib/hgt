import GaloisForLFunctions.HTGeometry.KleinbockMargulis.Nondegenerate
import GaloisForLFunctions.HTGeometry.KleinbockMargulis.LinearForms

/-!
# Proposition 2.3

At a nondegenerate point the measure of the set of parameters whose lattice `g_t Λ_{f(x)}` has a
short vector is at most `D (ε/ρ)^{1/dl}` times the measure of the ball.  This is Theorem 5.4 fed
with Proposition 3.4 for hypothesis (i) and with the linear independence of `1, f₁, …, f_n` for
hypothesis (ii); the latter is a compactness argument on the coefficient sphere.

## Main results

* `indep_of_nondegenerate` — nondegeneracy implies linear independence of `1, f₁, …, f_n` near the
  point.
* `exists_supGe` — hypothesis (ii) of Theorem 5.4.
* `prop_2_3` — the estimate `(2.6)`.
-/

open Set Metric MeasureTheory Filter
open scoped Topology

namespace GaloisForLFunctions.HTGeometry.KleinbockMargulis

variable {d n : ℕ}

/-- Nondegeneracy at `x₀` implies that `1, f₁, …, f_n` are linearly independent on any ball
around `x₀`. -/
theorem indep_of_nondegenerate {l : ℕ} {U : Set (Fin d → ℝ)}
    {F : (Fin d → ℝ) → (Fin n → ℝ)} (hF : ∀ y ∈ U, ContDiffAt ℝ ((l : ℕ)) F y)
    {x₀ : Fin d → ℝ}
    (hnd : ∀ w : Fin n → ℝ, (∀ j : ℕ, 1 ≤ j → j ≤ l → ∀ m : Fin j → (Fin d → ℝ),
        ∑ i, w i * (iteratedFDeriv ℝ j F x₀ m) i = 0) → w = 0)
    {r : ℝ} (hr : 0 < r) (hball : ball x₀ r ⊆ U) (c : Fin (n + 1) → ℝ)
    (hzero : ∀ x ∈ ball x₀ r, c 0 + ∑ i, c i.succ * F x i = 0) : c = 0 := by
  classical
  set w : Fin n → ℝ := fun i => c i.succ with hw
  have hcomb : comb w F =ᶠ[𝓝 x₀] fun _ => -c 0 := by
    filter_upwards [(isOpen_ball (x := x₀) (ε := r)).mem_nhds (mem_ball_self hr)] with x hx
    have := hzero x hx
    rw [comb]
    linarith
  have hw0 : w = 0 := by
    refine hnd w fun j hj1 hjl m => ?_
    have hcd : ContDiffAt ℝ ((j : ℕ)) F x₀ :=
      (hF x₀ (hball (mem_ball_self hr))).of_le (by exact_mod_cast hjl)
    rw [← iteratedFDeriv_comb hcd w m]
    have h1 : iteratedFDeriv ℝ j (comb w F) x₀ = iteratedFDeriv ℝ j (fun _ => -c 0) x₀ :=
      (Filter.EventuallyEq.iteratedFDeriv ℝ hcomb j).eq_of_nhds
    rw [h1, iteratedFDeriv_const_of_ne (by omega : j ≠ 0)]
    rfl
  have hc0 : c 0 = 0 := by
    have := hzero x₀ (mem_ball_self hr)
    have hsum : ∑ i, c i.succ * F x₀ i = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      have : w i = 0 := by rw [hw0]; rfl
      rw [hw] at this
      simp only at this
      rw [this, zero_mul]
    linarith
  funext i
  induction i using Fin.cases with
  | zero => exact hc0
  | succ i =>
      have : w i = 0 := by rw [hw0]; rfl
      rw [hw] at this
      exact this

/-- **Hypothesis (ii) of Theorem 5.4.**  Linear independence gives a uniform lower bound for the
supremum of a normalised combination. -/
theorem exists_supGe {F : (Fin d → ℝ) → (Fin n → ℝ)} {x₀ : Fin d → ℝ} {r : ℝ}
    (hindep : ∀ c : Fin (n + 1) → ℝ,
      (∀ x ∈ ball x₀ r, c 0 + ∑ i, c i.succ * F x i = 0) → c = 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ c : Fin (n + 1) → ℝ, 1 ≤ ‖c‖ →
      SupGe (fun x => c 0 + ∑ i, c i.succ * F x i) (ball x₀ r) ρ := by
  classical
  -- local data on the coefficient sphere
  have hlocal : ∀ c ∈ sphere (0 : Fin (n + 1) → ℝ) 1,
      ∃ (z : Fin d → ℝ) (s : ℝ) (N : Set (Fin (n + 1) → ℝ)), z ∈ ball x₀ r ∧ 0 < s ∧
        N ∈ 𝓝 c ∧ ∀ c' ∈ N, s < |c' 0 + ∑ i, c' i.succ * F z i| := by
    intro c hc
    have hc0 : c ≠ 0 := by
      intro h
      rw [mem_sphere_zero_iff_norm, h, norm_zero] at hc
      exact zero_ne_one hc
    have hex : ∃ z ∈ ball x₀ r, c 0 + ∑ i, c i.succ * F z i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hc0 (hindep c hcon)
    obtain ⟨z, hz, hzne⟩ := hex
    have hcontc : Continuous fun c' : Fin (n + 1) → ℝ => c' 0 + ∑ i, c' i.succ * F z i := by
      refine Continuous.add (continuous_apply 0) ?_
      exact continuous_finsetSum _ fun i _ => (continuous_apply i.succ).mul continuous_const
    set s : ℝ := |c 0 + ∑ i, c i.succ * F z i| / 2 with hsdef
    have hspos : 0 < s := by
      rw [hsdef]
      have := abs_pos.mpr hzne
      linarith
    have hslt : s < |c 0 + ∑ i, c i.succ * F z i| := by
      rw [hsdef]
      have := abs_pos.mpr hzne
      linarith
    refine ⟨z, s, {c' | s < |c' 0 + ∑ i, c' i.succ * F z i|}, hz, hspos, ?_, fun c' hc' => hc'⟩
    exact (hcontc.abs.continuousAt).eventually (eventually_gt_nhds hslt)
  choose! zf sf Nf hzf hsf hNf hboundf using hlocal
  obtain ⟨t, hts, hcover⟩ :=
    (isCompact_sphere (0 : Fin (n + 1) → ℝ) 1).elim_nhds_subcover Nf fun c hc => hNf c hc
  have hc₁ : (Pi.single (0 : Fin (n + 1)) (1 : ℝ)) ∈ sphere (0 : Fin (n + 1) → ℝ) 1 := by
    rw [mem_sphere_zero_iff_norm]
    exact norm_single_eq_one _
  obtain ⟨c₂, hc₂t, -⟩ := Set.mem_iUnion₂.mp (hcover hc₁)
  have ht : t.Nonempty := ⟨c₂, hc₂t⟩
  refine ⟨t.inf' ht sf, ?_, ?_⟩
  · rw [Finset.lt_inf'_iff]
    intro c hc
    exact hsf c (hts c hc)
  · intro c hc
    have hcn : (0:ℝ) < ‖c‖ := lt_of_lt_of_le one_pos hc
    have hwS : (‖c‖⁻¹ • c) ∈ sphere (0 : Fin (n + 1) → ℝ) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (ne_of_gt hcn)]
    obtain ⟨c', hc't, hc'N⟩ := Set.mem_iUnion₂.mp (hcover hwS)
    have hb := hboundf c' (hts c' hc't) _ hc'N
    refine supGe_of_mem (hzf c' (hts c' hc't)) ?_
    have hscale : (‖c‖⁻¹ • c) 0 + ∑ i, (‖c‖⁻¹ • c) i.succ * F (zf c') i
        = ‖c‖⁻¹ * (c 0 + ∑ i, c i.succ * F (zf c') i) := by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_add]
      refine congrArg _ ?_
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hscale, abs_mul, abs_of_pos (inv_pos.mpr hcn)] at hb
    have hfin : t.inf' ht sf ≤ sf c' := Finset.inf'_le sf hc't
    have hstep : ‖c‖⁻¹ * |c 0 + ∑ i, c i.succ * F (zf c') i| > t.inf' ht sf := by
      exact lt_of_le_of_lt hfin hb
    have hipos : 0 < t.inf' ht sf := by
      rw [Finset.lt_inf'_iff]
      intro cc hcc
      exact hsf cc (hts cc hcc)
    have hXpos : 0 < ‖c‖⁻¹ * |c 0 + ∑ i, c i.succ * F (zf c') i| := lt_trans hipos hstep
    have h2 : t.inf' ht sf ≤ ‖c‖ * (‖c‖⁻¹ * |c 0 + ∑ i, c i.succ * F (zf c') i|) := by
      nlinarith [hstep, mul_nonneg (sub_nonneg.mpr hc) hXpos.le]
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hcn), one_mul] at h2
    exact h2


theorem SupGe.mono_le {f : (Fin d → ℝ) → ℝ} {B : Set (Fin d → ℝ)} {ρ ρ' : ℝ}
    (h : SupGe f B ρ') (hρ : ρ ≤ ρ') : SupGe f B ρ :=
  fun c hc => h c (lt_of_lt_of_le hc hρ)

/-- **Proposition 2.3.** -/
theorem prop_2_3 [NeZero d] {l : ℕ} (hl : 1 ≤ l) {U : Set (Fin d → ℝ)} (hU : IsOpen U)
    {F : (Fin d → ℝ) → (Fin n → ℝ)} (hF : ∀ y ∈ U, ContDiffAt ℝ ((l : ℕ)) F y)
    {x₀ : Fin d → ℝ} (hx₀ : x₀ ∈ U)
    (hnd : ∀ w : Fin n → ℝ, (∀ j : ℕ, 1 ≤ j → j ≤ l → ∀ m : Fin j → (Fin d → ℝ),
        ∑ i, w i * (iteratedFDeriv ℝ j F x₀ m) i = 0) → w = 0) :
    ∃ r₀ D ρ : ℝ, 0 < r₀ ∧ 0 < D ∧ 0 < ρ ∧
      ∀ (t : Fin n → ℝ), (∀ i, 0 ≤ t i) → ∀ ε : ℝ, 0 < ε → ε ≤ ρ →
        volume {x ∈ ball x₀ r₀ | latticeDelta (flowMat t * unipotentMat fun i => F x i) < ε}
          ≤ ENNReal.ofReal (D * (ε / ρ) ^ (((d : ℝ) * (l : ℝ))⁻¹))
            * volume (ball x₀ r₀) := by
  classical
  have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hdR : (0:ℝ) < (d : ℝ) := by exact_mod_cast hdpos
  have hlR : (0:ℝ) < (l : ℝ) := by exact_mod_cast hl
  set α : ℝ := (((d : ℝ) * (l : ℝ))⁻¹) with hαdef
  have hα : 0 < α := by rw [hαdef]; positivity
  obtain ⟨ρ₃, C, hρ₃, hC, hgood₃⟩ := prop_3_4 hl hU hF hx₀ hnd
  obtain ⟨rU, hrU, hballU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx₀)
  set R : ℝ := min ρ₃ rU with hR
  have hRpos : 0 < R := lt_min hρ₃ hrU
  have hpow : (0:ℝ) < (3 : ℝ) ^ (n + 1) := by positivity
  set r₀ : ℝ := R / (3 : ℝ) ^ (n + 1) with hr₀def
  have hr₀ : 0 < r₀ := by rw [hr₀def]; positivity
  have hbig : (3 : ℝ) ^ (n + 1) * r₀ = R := by
    rw [hr₀def]
    field_simp
  have hsubU : ball x₀ ((3 : ℝ) ^ (n + 1) * r₀) ⊆ U := by
    rw [hbig]
    exact subset_trans (ball_subset_ball (min_le_right _ _)) hballU
  have hsub₃ : ball x₀ ((3 : ℝ) ^ (n + 1) * r₀) ⊆ ball x₀ ρ₃ := by
    rw [hbig]
    exact ball_subset_ball (min_le_left _ _)
  have hr₀U : ball x₀ r₀ ⊆ U := by
    refine subset_trans (ball_subset_ball ?_) hsubU
    nlinarith [hr₀, one_le_pow₀ (by norm_num : (1:ℝ) ≤ 3) (n := n + 1)]
  -- hypothesis (i)
  have hgood : ∀ c : Fin (n + 1) → ℝ,
      IsGood C α (fun x => c 0 + ∑ i, c i.succ * F x i) (ball x₀ ((3 : ℝ) ^ (n + 1) * r₀)) := by
    intro c
    exact (hgood₃ (c 0) (fun i => c i.succ)).mono_set hsub₃
  -- hypothesis (ii)
  have hindep := indep_of_nondegenerate hF hnd hr₀ hr₀U
  obtain ⟨ρ', hρ'pos, hsup'⟩ := exists_supGe hindep
  set ρ : ℝ := min ρ' (1 / ((n : ℝ) + 1)) with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]
    exact lt_min hρ'pos (by positivity)
  have hρk : ((n : ℝ) + 1) * ρ ≤ 1 := by
    have h1 : ρ ≤ 1 / ((n : ℝ) + 1) := min_le_right _ _
    have h2 : (0:ℝ) < (n : ℝ) + 1 := by positivity
    rw [le_div_iff₀ h2] at h1
    linarith
  have hsup : ∀ c : Fin (n + 1) → ℝ, 1 ≤ ‖c‖ →
      SupGe (fun x => c 0 + ∑ i, c i.succ * F x i) (ball x₀ r₀) ρ :=
    fun c hc => (hsup' c hc).mono_le (min_le_left _ _)
  -- continuity
  have hfcont : ∀ i : Fin n,
      ContinuousOn (fun x => F x i) (ball x₀ ((3 : ℝ) ^ (n + 1) * r₀)) := by
    intro i y hy
    have h1 : ContinuousAt F y := (hF y (hsubU hy)).continuousAt
    exact ((continuous_apply i).continuousAt.comp h1).continuousWithinAt
  -- Theorem 5.4
  have hNpos : (0:ℝ) < (Besicovitch.multiplicity (Fin d → ℝ) : ℝ) := by
    have := one_le_besicovitch_multiplicity (d := d)
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one this
  refine ⟨r₀, ((n : ℝ) + 1) * C
      * ((3 : ℝ) ^ d * (Besicovitch.multiplicity (Fin d → ℝ) : ℝ)) ^ (n + 1), ρ, hr₀,
    by positivity, hρpos, ?_⟩
  intro t ht ε hε hερ
  exact theorem_5_4 hC hα hρpos hρk hr₀ hfcont hgood hsup ht hε hερ

end GaloisForLFunctions.HTGeometry.KleinbockMargulis
