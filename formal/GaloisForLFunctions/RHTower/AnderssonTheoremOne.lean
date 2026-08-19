import GaloisForLFunctions.RHTower.AnderssonRemainderRepresentation
import GaloisForLFunctions.RHTower.Sieve.CharacterStacking
import GaloisForLFunctions.HTGeometry.HalfPlaneMellinAnalytic
import GaloisForLFunctions.HTGeometry.HalfPlaneSequenceGluing
import GaloisForLFunctions.HTGeometry.DatumNormalization

/-!
# Andersson's Theorem 1

The Mellin datum of a half-plane analytic function is, up to an entire function, the `L`-series of
the von Mangoldt weights of a Helson character.  The character comes from the window recursion, the
identity from the iterated Mellin representation, and the entire function from gluing the
representations of all orders: the `j`-th one converges on `Re s > (j+1)ϑ + 2θ - j`, an abscissa
that decreases to `-∞` because `ϑ = θ + (1-θ)/3 < 1`.
-/

noncomputable section

open MeasureTheory Filter Set Asymptotics ArithmeticFunction GaloisForLFunctions.HTGeometry

namespace RHTower

/-- The abscissa at which the `j`-th Mellin representation converges. -/
def anderssonAbscissa (θ : ℝ) (j : ℕ) : ℝ := ((j : ℝ) + 1) * (θ + (1 - θ) / 3) + 2 * θ - j

theorem anderssonAbscissa_zero (θ : ℝ) :
    anderssonAbscissa θ 0 = (θ + (1 - θ) / 3) + 2 * θ := by
  rw [anderssonAbscissa]
  push_cast
  ring

theorem anderssonAbscissa_le_zero {θ : ℝ} (hθ1 : θ < 1) (j : ℕ) :
    anderssonAbscissa θ j ≤ anderssonAbscissa θ 0 := by
  have hj : (0:ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  rw [anderssonAbscissa, anderssonAbscissa_zero]
  nlinarith [hj, hθ1]

theorem anderssonAbscissa_unbounded {θ : ℝ} (hθ1 : θ < 1) (C : ℝ) :
    ∃ n : ℕ, anderssonAbscissa θ n < C := by
  set ϑ : ℝ := θ + (1 - θ) / 3 with hϑdef
  have hϑ1 : ϑ < 1 := by
    rw [hϑdef]
    linarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((ϑ + 2 * θ - C) / (1 - ϑ))
  refine ⟨n, ?_⟩
  have hpos : 0 < 1 - ϑ := by linarith
  rw [div_lt_iff₀ hpos] at hn
  rw [anderssonAbscissa, ← hϑdef]
  nlinarith [hn]

theorem two_lt_anderssonAbscissa_zero {θ : ℝ} (hθ23 : 2/3 < θ) :
    2 < anderssonAbscissa θ 0 := by
  rw [anderssonAbscissa_zero]
  linarith

/-- **Andersson's Theorem 1.**  A bounded, vanishing Mellin datum is the `L`-series of a Helson
character's von Mangoldt weights, plus an entire function. -/
theorem exists_character_entire_remainder {α θ : ℝ}
    (halpha : (701299/1000000:ℝ) < α) (hαθ : α < θ) (hθ1 : θ < 1) (hθ23 : 2/3 < θ)
    {q : ℝ → ℂ} (hqmeas : AEStronglyMeasurable q (volume.restrict (Set.Ioi (1:ℝ))))
    (hq0 : Tendsto q atTop (nhds 0)) {M : ℝ} (hqb : ∀ x : ℝ, 1 ≤ x → ‖q x‖ ≤ M) :
    ∃ (u : ℕ → ℂ) (g : ℂ → ℂ), (∀ n, ‖u n‖ = 1) ∧ Differentiable ℂ g ∧
      ∀ s : ℂ, anderssonAbscissa θ 0 < s.re →
        (∫ x in Set.Ioi (1:ℝ), q x * (x : ℂ) ^ (-s))
          = LSeries (characterSource u) s + g s := by
  classical
  have hα0 : 0 < α := lt_trans (by norm_num : (0:ℝ) < 701299/1000000) halpha
  have hθ0 : 0 < θ := lt_trans hα0 hαθ
  set ϑ : ℝ := θ + (1 - θ) / 3 with hϑdef
  -- the normalized datum
  set dq : ℝ → ℂ := truncDatum q with hdqdef
  set Mg : ℝ := max M 0 with hMgdef
  have hMg0 : 0 ≤ Mg := le_max_right _ _
  have hdqb : ∀ t : ℝ, ‖dq t‖ ≤ Mg := norm_truncDatum_le hqb
  have hdqint : ∀ u v : ℝ, IntervalIntegrable dq volume u v :=
    intervalIntegrable_truncDatum hqmeas hqb
  have hdqtend : Tendsto dq atTop (nhds 0) := tendsto_truncDatum hq0
  -- the negated datum, which is what the recursion consumes
  set ndq : ℝ → ℂ := fun t => -dq t with hndqdef
  have hndqint : ∀ u v : ℝ, IntervalIntegrable ndq volume u v := fun u v => (hdqint u v).neg
  have hndqb : ∀ t : ℝ, ‖ndq t‖ ≤ Mg := by
    intro t
    rw [hndqdef, norm_neg]
    exact hdqb t
  have hndqtend : Tendsto ndq atTop (nhds 0) := by
    have := hdqtend.neg
    rw [neg_zero] at this
    exact this
  obtain ⟨u, hu1, hu2⟩ :=
    Sieve.exists_andersson_character halpha hαθ hθ1 hθ23 hndqint hndqb hndqtend
  set a : ℕ → ℂ := fun n => -characterSource u n with hadef
  -- the level bounds transported to the chain of `dq` and `a`
  have hchain : ∀ (j : ℕ) (y : ℝ),
      arithJumpProfile dq a j y = -(arithJumpProfile ndq (characterSource u) j y) := by
    intro j y
    have hfun : (fun t => -(ndq t)) = dq := by
      funext t
      rw [hndqdef, neg_neg]
    have := arithJumpProfile_neg ndq (characterSource u) j y
    rw [hfun] at this
    exact this
  have hlevel : ∀ j : ℕ, ∃ X : ℝ, 1 ≤ X ∧ ∀ x : ℝ, X ≤ x →
      ‖arithJumpProfile dq a j x‖ ≤ x ^ (((j : ℝ) + 1) * ϑ + 2 * θ) * Real.log x := by
    intro j
    obtain ⟨X, hX1, hX⟩ := hu2 j
    refine ⟨X, hX1, fun x hx => ?_⟩
    rw [hchain j x, norm_neg]
    exact hX x hx
  -- the arithmetic partial sums
  obtain ⟨Cψ, hCψ0, hCψ⟩ := exists_chebyshevPsiReal_le_linear
  have hpartial : ∀ N : ℕ, ‖∑ m ∈ Finset.Icc 1 N, a m‖ ≤ Cψ * (N : ℝ) ^ (1:ℝ) := by
    intro N
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      have hempty : Finset.Icc 1 0 = (∅ : Finset ℕ) := by
        exact Finset.Icc_eq_empty (by omega)
      rw [hempty, Finset.sum_empty, norm_zero]
      positivity
    · have hN1 : (1:ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hcrude := Sieve.norm_arithProfile_characterSource_le_crude (fun p _ => hu1 p) hCψ hN1 0
      rw [arithProfile_zero] at hcrude
      have hfloor : ⌊(N : ℝ)⌋₊ = N := Nat.floor_natCast N
      rw [hfloor] at hcrude
      have hsum : ∑ m ∈ Finset.Icc 1 N, a m = -∑ m ∈ Finset.Icc 1 N, characterSource u m := by
        rw [hadef, ← Finset.sum_neg_distrib]
      rw [hsum, norm_neg]
      refine le_trans hcrude ?_
      rw [Real.rpow_one]
      have h0 : ((0:ℕ).factorial : ℝ) = 1 := by norm_num
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
      linarith
  -- summability of the source
  have hsummable : ∀ s : ℂ, 2 < s.re → LSeriesSummable a s := by
    intro s hs
    refine LSeriesSummable_of_isBigO_rpow (x := 2) hs ?_
    refine IsBigO.of_bound 1 (Filter.Eventually.of_forall fun n => ?_)
    have hnorm : ‖a n‖ = Λ n := by
      rw [hadef, norm_neg]
      exact norm_characterSource_eq (fun p _ => hu1 p) n
    have hle : (Λ n : ℝ) ≤ (n : ℝ) := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        simp
      · have hn1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have hlog := vonMangoldt_le_log (n := n)
        have hlogle : Real.log n ≤ (n : ℝ) - 1 :=
          Real.log_le_sub_one_of_pos (by linarith)
        linarith
    rw [hnorm]
    have hpow : ‖(n : ℝ) ^ ((2:ℝ) - 1)‖ = (n : ℝ) := by
      have : (2:ℝ) - 1 = 1 := by norm_num
      rw [this, Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)]
    rw [hpow, one_mul]
    exact hle
  -- integrability of the datum transform
  have hdatumint : ∀ s : ℂ, 1 < s.re →
      IntegrableOn (fun t : ℝ => dq t * (t : ℂ) ^ (-s)) (Set.Ioi (1:ℝ)) := by
    intro s hs
    refine integrableOn_halfPlaneMellin (ρ := 0) (X := max (Real.exp Mg) 1)
      (le_max_right _ _) (fun y _ => hdqint 1 y) ?_ (by simpa using hs)
    intro x hx
    have hx1 : (1:ℝ) ≤ x := le_trans (le_max_right _ _) hx
    have hxe : Real.exp Mg ≤ x := le_trans (le_max_left _ _) hx
    have hlog : Mg ≤ Real.log x := by
      have := Real.log_le_log (Real.exp_pos Mg) hxe
      rwa [Real.log_exp] at this
    have : x ^ (0:ℝ) = 1 := Real.rpow_zero x
    rw [this, one_mul]
    exact le_trans (hdqb x) hlog
  -- integrability of every level
  have hlevelint : ∀ (j : ℕ) (s : ℂ), anderssonAbscissa θ j < s.re →
      IntegrableOn
        (fun t : ℝ => arithJumpProfile dq a j t * (t : ℂ) ^ (-(s + 1 + (j : ℂ)))) (Set.Ioi (1:ℝ)) := by
    intro j s hs
    obtain ⟨X, hX1, hX⟩ := hlevel j
    refine integrableOn_halfPlaneMellin (ρ := ((j : ℝ) + 1) * ϑ + 2 * θ) (X := X) hX1
      (fun y hy => intervalIntegrable_arithJumpProfile hdqint a j hy) hX ?_
    have hre : (s + 1 + (j : ℂ)).re = s.re + 1 + (j : ℝ) := by
      simp
    rw [hre]
    rw [anderssonAbscissa, ← hϑdef] at hs
    linarith
  -- the representations
  set H : ℕ → ℂ → ℂ := fun j s => s * (∏ i ∈ Finset.range j, (s + 1 + (i : ℂ))) *
    halfPlaneMellin (arithJumpProfile dq a j) (s + 1 + (j : ℂ)) with hHdef
  have hrep : ∀ (j : ℕ) (s : ℂ), anderssonAbscissa θ 0 < s.re →
      (∫ x in Set.Ioi (1:ℝ), dq x * (x : ℂ) ^ (-s)) + LSeries a s = H j s := by
    intro j s hs
    have hs2 : 2 < s.re := lt_trans (two_lt_anderssonAbscissa_zero hθ23) hs
    have hs1 : 1 < s.re := by linarith
    have hs0 : 0 < s.re := by linarith
    exact mellin_representation_iterated hdqint hCψ0.le hpartial hs0 (by simpa using hs1)
      (hsummable s hs2) (hdatumint s hs1)
      (fun k => hlevelint k s (lt_of_le_of_lt (anderssonAbscissa_le_zero hθ1 k) hs)) j
  have hHagree : ∀ (j : ℕ) (s : ℂ), anderssonAbscissa θ 0 < s.re → H j s = H 0 s := by
    intro j s hs
    rw [← hrep j s hs, hrep 0 s hs]
  have hHdiff : ∀ (j : ℕ) (s : ℂ), anderssonAbscissa θ j < s.re → DifferentiableAt ℂ (H j) s := by
    intro j s hs
    obtain ⟨X, hX1, hX⟩ := hlevel j
    have hshift : DifferentiableAt ℂ (fun z : ℂ => z + 1 + (j : ℂ)) s :=
      ((differentiableAt_id).add_const 1).add_const _
    have hmel : DifferentiableAt ℂ (halfPlaneMellin (arithJumpProfile dq a j))
        (s + 1 + (j : ℂ)) := by
      refine differentiableAt_halfPlaneMellin (ρ := ((j : ℝ) + 1) * ϑ + 2 * θ) (X := X) hX1
        (fun y hy => intervalIntegrable_arithJumpProfile hdqint a j hy) hX ?_
      have hre : (s + 1 + (j : ℂ)).re = s.re + 1 + (j : ℝ) := by simp
      rw [hre]
      rw [anderssonAbscissa, ← hϑdef] at hs
      linarith
    have hcomp : DifferentiableAt ℂ
        (fun z : ℂ => halfPlaneMellin (arithJumpProfile dq a j) (z + 1 + (j : ℂ))) s := by
      have := DifferentiableAt.comp s hmel hshift
      simpa [Function.comp_def] using this
    have hpoly : DifferentiableAt ℂ
        (fun z : ℂ => z * ∏ i ∈ Finset.range j, (z + 1 + (i : ℂ))) s := by
      refine differentiableAt_id.mul ?_
      have : Differentiable ℂ (fun z : ℂ => ∏ i ∈ Finset.range j, (z + 1 + (i : ℂ))) := by
        have hprod : (fun z : ℂ => ∏ i ∈ Finset.range j, (z + 1 + (i : ℂ)))
            = ∏ i ∈ Finset.range j, (fun z : ℂ => z + 1 + (i : ℂ)) := by
          funext z
          rw [Finset.prod_apply]
        rw [hprod]
        refine Differentiable.finsetProd ?_
        intro i _
        exact fun z => ((differentiableAt_id).add_const 1).add_const _
      exact this s
    exact hpoly.mul hcomp
  obtain ⟨g₀, hg₀diff, hg₀⟩ := exists_entire_of_halfPlane_family
    (A := anderssonAbscissa θ) (H := H) (A₀ := anderssonAbscissa θ 0)
    (anderssonAbscissa_unbounded hθ1) hHdiff hHagree
  refine ⟨u, g₀, hu1, hg₀diff, ?_⟩
  intro s hs
  have hid := hrep 0 s hs
  have hg : g₀ s = H 0 s := hg₀ 0 s hs
  have hLneg : LSeries a s = -LSeries (characterSource u) s := by
    rw [hadef, LSeries, LSeries, ← tsum_neg]
    refine tsum_congr fun n => ?_
    rw [LSeries.term_def, LSeries.term_def]
    by_cases hn : n = 0
    · rw [if_pos hn, if_pos hn, neg_zero]
    · rw [if_neg hn, if_neg hn, neg_div]
  rw [setIntegral_truncDatum] at hid
  rw [hLneg] at hid
  rw [hg, ← hid]
  ring

end RHTower

end
