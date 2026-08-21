/-
# The gap theorem for a single non-rational algebraic germ

Combining the algebraic layer (`GermIntegral`, `ReflectSubstitution`, `IntegerRoot`) with the
analytic layer (`TaylorTail`), this file proves the core dichotomy of Coleman--Zwald: if `w` is
analytic at an integer point `s₀`, integral over `ℤ[X]` as a germ, and is *not* a rational function
near `s₀`, then the set of integers `n` with `w (s₀ + 1/n) ∈ ℚ` is gap thin.
-/
import GaloisForLFunctions.HTGeometry.HilbertIrreducibility.ReflectSubstitution
import GaloisForLFunctions.HTGeometry.HilbertIrreducibility.IntegerRoot
import GaloisForLFunctions.HTGeometry.HilbertIrreducibility.TaylorTail
import GaloisForLFunctions.HTGeometry.HilbertIrreducibility.RationalInterpolation
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Analytic.Polynomial

namespace GaloisForLFunctions.HTGeometry.HilbertIrreducibility

open Polynomial Filter Topology

/-- `w` agrees near `s₀` with a quotient of polynomials with rational coefficients, the denominator
being nonzero *at* `s₀`. -/
def IsRatGerm (s₀ : ℂ) (w : ℂ → ℂ) : Prop :=
  ∃ p q : Polynomial ℚ, Polynomial.aeval s₀ q ≠ 0 ∧
    ∀ᶠ s in 𝓝 s₀, (Polynomial.aeval s q) * w s = Polynomial.aeval s p

/-- **Integrality of the scaled values.**  If `w` is integral over `ℤ[X]` as a germ at the integer
point `s₀`, then `n ^ D * w (s₀ + 1/n)` is an integer whenever it is rational and `n` is large. -/
theorem exists_int_value {s₀ : ℤ} {w : ℂ → ℂ}
    (hint : IsIntegral (Polynomial ℤ) ((w : ℂ → ℂ) : Germ (𝓝 ((s₀ : ℤ) : ℂ)) ℂ)) :
    ∃ (D : ℕ) (T : ℝ), ∀ n : ℤ, T < (n : ℝ) → ∀ c : ℚ,
      w (((s₀ : ℤ) : ℂ) + ((n : ℤ) : ℂ)⁻¹) = (c : ℂ) → ∃ N : ℤ, ((n : ℚ)) ^ D * c = (N : ℚ) := by
  classical
  obtain ⟨P, hPmonic, hPdeg, hPrel⟩ := exists_monic_bivariate_of_isIntegral hint
  set M : ℕ := P.natDegree with hM
  set D : ℕ := (Finset.range (M + 1)).sup fun j => (P.coeff j).natDegree with hDdef
  have hD : ∀ j, (P.coeff j).natDegree ≤ D := by
    intro j
    by_cases hj : j ≤ M
    · exact Finset.le_sup (f := fun j => (P.coeff j).natDegree) (Finset.mem_range.mpr (by omega))
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      simp
  set Q : Polynomial (Polynomial ℤ) := shiftedPoly s₀ D M P with hQdef
  have hQmonic : Q.Monic := monic_shiftedPoly s₀ D M P
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp hPrel
  refine ⟨D, max ρ⁻¹ 1, fun n hn c hc => ?_⟩
  have hn1 : (1 : ℝ) < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_trans zero_lt_one hn1
  have hnC : ((n : ℤ) : ℂ) ≠ 0 := by
    intro h
    have : (n : ℝ) = 0 := by exact_mod_cast congrArg Complex.re h
    linarith
  have hdist : dist (((n : ℤ) : ℂ)⁻¹ + ((s₀ : ℤ) : ℂ)) (((s₀ : ℤ) : ℂ)) < ρ := by
    have habs : ‖(((n : ℤ) : ℂ))⁻¹‖ = ((n : ℝ))⁻¹ := by
      rw [norm_inv]
      congr 1
      simp [abs_of_pos hnpos]
    rw [Complex.dist_eq, add_sub_cancel_right, habs]
    have hρi : ρ⁻¹ < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
    exact inv_lt_of_inv_lt₀ hρ hρi
  have hrel : bivEval P (((n : ℤ) : ℂ)⁻¹ + ((s₀ : ℤ) : ℂ))
      (w (((n : ℤ) : ℂ)⁻¹ + ((s₀ : ℤ) : ℂ))) = 0 := hball hdist
  have hwval : w (((n : ℤ) : ℂ)⁻¹ + ((s₀ : ℤ) : ℂ)) = (c : ℂ) := by
    rw [add_comm]; exact hc
  have hs₀ : (algebraMap ℤ ℂ) s₀ = ((s₀ : ℤ) : ℂ) := by simp
  rw [hwval] at hrel
  have hshift := bivEval_shiftedPoly (R := ℤ) s₀ D M hD hM.symm hPmonic
    (t := ((n : ℤ) : ℂ)) (w := (c : ℂ)) hnC
  rw [hs₀, hrel, mul_zero] at hshift
  have hcast : ((n : ℤ) : ℂ) ^ D * (c : ℂ) = (((n : ℚ) ^ D * c : ℚ) : ℂ) := by
    push_cast
    ring
  rw [hcast] at hshift
  exact exists_int_of_bivEval hQmonic hshift

/-! ### Real and imaginary parts of the shifted germ -/

/-- The shifted function `x ↦ w (s₀ + x)` is analytic at `0`. -/
theorem analyticAt_shift {s₀ : ℂ} {w : ℂ → ℂ} (hw : AnalyticAt ℂ w s₀) :
    AnalyticAt ℂ (fun x : ℂ => w (s₀ + x)) 0 := by
  have haff : AnalyticAt ℂ (fun x : ℂ => s₀ + x) 0 := analyticAt_const.add analyticAt_id
  refine AnalyticAt.fun_comp ?_ haff
  simpa using hw

theorem analyticAt_re_shift {s₀ : ℂ} {w : ℂ → ℂ} (hw : AnalyticAt ℂ w s₀) :
    AnalyticAt ℝ (fun x : ℝ => (w (s₀ + (x : ℂ))).re) 0 := by
  have h1 : AnalyticAt ℝ (fun x : ℂ => w (s₀ + x)) (((0 : ℝ) : ℂ)) := by
    have := (analyticAt_shift hw).restrictScalars (𝕜 := ℝ)
    simpa using this
  have h2 : AnalyticAt ℝ (fun x : ℝ => ((x : ℂ))) 0 := Complex.ofRealCLM.analyticAt 0
  exact (Complex.reCLM.analyticAt _).fun_comp (h1.fun_comp h2)

theorem analyticAt_im_shift {s₀ : ℂ} {w : ℂ → ℂ} (hw : AnalyticAt ℂ w s₀) :
    AnalyticAt ℝ (fun x : ℝ => (w (s₀ + (x : ℂ))).im) 0 := by
  have h1 : AnalyticAt ℝ (fun x : ℂ => w (s₀ + x)) (((0 : ℝ) : ℂ)) := by
    have := (analyticAt_shift hw).restrictScalars (𝕜 := ℝ)
    simpa using this
  have h2 : AnalyticAt ℝ (fun x : ℝ => ((x : ℂ))) 0 := Complex.ofRealCLM.analyticAt 0
  exact (Complex.imCLM.analyticAt _).fun_comp (h1.fun_comp h2)

/-! ### The core dichotomy -/

/-- **The core gap theorem.**  If `w` is analytic at an integer point `s₀`, integral over `ℤ[X]` as
a germ there, and not a rational function near `s₀`, then the set of integers `n` for which
`w (s₀ + 1/n)` is rational is gap thin. -/
theorem thin_of_not_isRatGerm {s₀ : ℤ} {w : ℂ → ℂ}
    (hw : AnalyticAt ℂ w (((s₀ : ℤ) : ℂ)))
    (hint : IsIntegral (Polynomial ℤ) ((w : ℂ → ℂ) : Germ (𝓝 ((s₀ : ℤ) : ℂ)) ℂ))
    (hnr : ¬ IsRatGerm (((s₀ : ℤ) : ℂ)) w) :
    Thin {n : ℤ | ∃ c : ℚ, w (((s₀ : ℤ) : ℂ) + ((n : ℤ) : ℂ)⁻¹) = (c : ℂ)} := by
  classical
  obtain ⟨D, T₀, hval⟩ := exists_int_value hint
  set S : Set ℤ := {n : ℤ | ∃ c : ℚ, w (((s₀ : ℤ) : ℂ) + ((n : ℤ) : ℂ)⁻¹) = (c : ℂ)} with hS
  set g : ℝ → ℝ := fun x => (w (((s₀ : ℤ) : ℂ) + (x : ℂ))).re with hgdef
  set ψ : ℝ → ℝ := fun x => (w (((s₀ : ℤ) : ℂ) + (x : ℂ))).im with hψdef
  have hgA : AnalyticAt ℝ g 0 := analyticAt_re_shift hw
  have hψA : AnalyticAt ℝ ψ 0 := analyticAt_im_shift hw
  -- the cast identity used throughout
  have hcastinv : ∀ n : ℤ, (0 : ℝ) < (n : ℝ) →
      ((((n : ℝ))⁻¹ : ℝ) : ℂ) = ((n : ℤ) : ℂ)⁻¹ := by
    intro n _
    push_cast
    ring
  rcases hψA.eventually_eq_zero_or_eventually_ne_zero with hb | hb
  · -- the imaginary part vanishes identically near `0`: the real branch takes over
    obtain ⟨ρ₁, hρ₁, hball₁⟩ := Metric.eventually_nhds_iff.mp hb
    set T : ℝ := max (max T₀ ρ₁⁻¹) 1 with hTdef
    have hTinv : ∀ n : ℤ, T < (n : ℝ) →
        (0 : ℝ) < (n : ℝ) ∧ T₀ < (n : ℝ) ∧ |((n : ℝ))⁻¹| < ρ₁ := by
      intro n hn
      have h1 : (1 : ℝ) < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
      have hpos : (0 : ℝ) < (n : ℝ) := lt_trans zero_lt_one h1
      refine ⟨hpos, lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hn, ?_⟩
      have h2 : ρ₁⁻¹ < (n : ℝ) := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hn
      rw [abs_of_pos (by positivity)]
      exact inv_lt_of_inv_lt₀ hρ₁ h2
    have hreal : ∀ n : ℤ, T < (n : ℝ) → ∀ c : ℚ,
        w (((s₀ : ℤ) : ℂ) + ((n : ℤ) : ℂ)⁻¹) = (c : ℂ) → g ((n : ℝ))⁻¹ = (c : ℝ) := by
      intro n hn c hc
      have hx := hTinv n hn
      have : w (((s₀ : ℤ) : ℂ) + ((((n : ℝ))⁻¹ : ℝ) : ℂ)) = (c : ℂ) := by
        rw [hcastinv n hx.1]; exact hc
      simp only [hgdef, this]
      simp
    have hintval : ∀ n ∈ {n : ℤ | n ∈ S ∧ T < (n : ℝ)},
        ∃ N : ℤ, ((n : ℝ)) ^ D * g ((n : ℝ))⁻¹ = (N : ℝ) := by
      rintro n ⟨⟨c, hc⟩, hn⟩
      obtain ⟨N, hN⟩ := hval n (hTinv n hn).2.1 c hc
      refine ⟨N, ?_⟩
      rw [hreal n hn c hc]
      have : ((n : ℝ)) ^ D * (c : ℝ) = (((n : ℚ) ^ D * c : ℚ) : ℝ) := by push_cast; ring
      rw [this, hN]
      push_cast
      ring
    rcases thin_or_eventually_poly D hgA {n : ℤ | n ∈ S ∧ T < (n : ℝ)} hintval with hthin | hpoly
    · exact thin_of_inter hthin
    · obtain ⟨p, hpdeg, T', hp⟩ := hpoly
      by_cases hrat : ∀ i, ∃ q : ℚ, p.coeff i = (q : ℝ)
      · -- all coefficients rational: `w` is a rational germ, contradicting the hypothesis
        exfalso
        apply hnr
        choose cq hcq using hrat
        set pq : Polynomial ℚ :=
          ∑ i ∈ Finset.range (D + 1), Polynomial.monomial i (cq i) with hpqdef
        have hpqdeg : pq.natDegree ≤ D := by
          refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
          exact le_trans (Polynomial.natDegree_monomial_le _)
            (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
        have hpqmap : pq.map (algebraMap ℚ ℝ) = p := by
          rw [hpqdef, Polynomial.map_sum]
          simp only [Polynomial.map_monomial]
          rw [Polynomial.as_sum_range' p (D + 1) (by omega)]
          refine Finset.sum_congr rfl fun i _ => ?_
          congr 1
          rw [eq_ratCast (algebraMap ℚ ℝ) (cq i), ← hcq i]
        set A : Polynomial ℚ := shiftReflect (0 : ℚ) D pq with hAdef
        set Pfin : Polynomial ℚ :=
          A.comp (Polynomial.X - Polynomial.C (((s₀ : ℤ) : ℚ))) with hPfindef
        refine ⟨Pfin, 1, by simp, ?_⟩
        -- the two analytic functions agree along `s₀ + 1/t`, `t → ∞`
        set F : ℝ → ℂ := fun t => ((s₀ : ℤ) : ℂ) + ((t : ℝ) : ℂ)⁻¹ with hFdef
        have hFtend0 : Filter.Tendsto (fun t : ℝ => ((t : ℝ) : ℂ)⁻¹) Filter.atTop (𝓝 0) := by
          rw [tendsto_zero_iff_norm_tendsto_zero]
          simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs]
          exact tendsto_inv_atTop_zero.comp tendsto_abs_atTop_atTop
        have hFtend : Filter.Tendsto F Filter.atTop (𝓝 ((s₀ : ℤ) : ℂ)) := by
          have := (tendsto_const_nhds (x := ((s₀ : ℤ) : ℂ)) (f := Filter.atTop (α := ℝ))).add
            hFtend0
          simpa [hFdef] using this
        have hFne : ∀ᶠ t : ℝ in Filter.atTop, F t ∈ ({((s₀ : ℤ) : ℂ)}ᶜ : Set ℂ) := by
          filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff, hFdef]
          intro hcon
          have : ((t : ℝ) : ℂ)⁻¹ = 0 := by
            have := hcon
            linear_combination this
          have htc : ((t : ℝ) : ℂ) = 0 := by
            simpa using congrArg (fun z : ℂ => z⁻¹) this
          have : (t : ℝ) = 0 := by exact_mod_cast htc
          linarith
        have hFwithin : Filter.Tendsto F Filter.atTop (𝓝[≠] ((s₀ : ℤ) : ℂ)) :=
          tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within F hFtend hFne
        -- the pointwise identity along the sequence
        have hpoint : ∀ᶠ t : ℝ in Filter.atTop, w (F t) = Polynomial.aeval (F t) Pfin := by
          filter_upwards [Filter.eventually_gt_atTop (max (max T' ρ₁⁻¹) 1)] with t ht
          have ht1 : (1 : ℝ) < t := lt_of_le_of_lt (le_max_right _ _) ht
          have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht1
          have htT' : T' < t := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) ht
          have htρ : ρ₁⁻¹ < t := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) ht
          have htinv : |t⁻¹| < ρ₁ := by
            rw [abs_of_pos (by positivity)]
            exact inv_lt_of_inv_lt₀ hρ₁ htρ
          have hψ0 : ψ t⁻¹ = 0 := hball₁ (by rw [Real.dist_eq, sub_zero]; exact htinv)
          have htC : ((t : ℝ) : ℂ) ≠ 0 := by
            simpa using ne_of_gt ht0
          have hFval : F t = ((s₀ : ℤ) : ℂ) + ((t⁻¹ : ℝ) : ℂ) := by
            rw [hFdef]; push_cast; ring
          have hwval : w (F t) = ((g t⁻¹ : ℝ) : ℂ) := by
            rw [hFval]
            apply Complex.ext
            · simp [hgdef]
            · simpa [hψdef] using hψ0
          have hgval : (t : ℝ) ^ D * g t⁻¹ = p.eval t := hp t htT'
          -- the polynomial side
          have hcomp : Polynomial.aeval (F t) Pfin
              = Polynomial.aeval (((t : ℝ) : ℂ)⁻¹) A := by
            rw [hPfindef, Polynomial.aeval_comp]
            congr 1
            rw [hFdef]
            simp
          have hA : Polynomial.aeval (((t : ℝ) : ℂ)⁻¹) A
              = (((t : ℝ) : ℂ)⁻¹) ^ D * Polynomial.aeval ((t : ℝ) : ℂ) pq := by
            have h := eval_shiftReflect (R := ℚ) (0 : ℚ) D pq hpqdeg
              (t := ((t : ℝ) : ℂ)⁻¹) (inv_ne_zero htC)
            rw [hAdef, h]
            simp
          have hpqC : Polynomial.aeval ((t : ℝ) : ℂ) pq = ((p.eval t : ℝ) : ℂ) := by
            have h1 : Polynomial.aeval ((t : ℝ) : ℂ) pq
                = Polynomial.aeval ((t : ℝ) : ℂ) (pq.map (algebraMap ℚ ℝ)) := by
              rw [Polynomial.aeval_map_algebraMap]
            rw [h1, hpqmap, Polynomial.aeval_def]
            have h2 := Polynomial.eval₂_at_apply (p := p) (algebraMap ℝ ℂ) t
            simpa using h2
          rw [hwval, hcomp, hA, hpqC]
          have hDinv : (((t : ℝ) : ℂ)⁻¹) ^ D * ((p.eval t : ℝ) : ℂ)
              = ((t⁻¹ ^ D * p.eval t : ℝ) : ℂ) := by push_cast; ring
          have hcancel : (t : ℝ)⁻¹ ^ D * (t ^ D * g t⁻¹) = g t⁻¹ := by
            rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ (ne_of_gt ht0), one_pow, one_mul]
          rw [hDinv, ← hgval, hcancel]
        -- upgrade to an eventual identity by the identity theorem
        have hidA : AnalyticAt ℂ (fun s : ℂ => s) (((s₀ : ℤ) : ℂ)) := analyticAt_id
        have hanaP : AnalyticAt ℂ (fun s : ℂ => Polynomial.aeval s Pfin) (((s₀ : ℤ) : ℂ)) :=
          AnalyticAt.aeval_polynomial hidA Pfin
        have hfreq : ∃ᶠ z in 𝓝[≠] (((s₀ : ℤ) : ℂ)), w z = Polynomial.aeval z Pfin :=
          hFwithin.frequently hpoint.frequently
        have heq := (hw.frequently_eq_iff_eventually_eq hanaP).mp hfreq
        filter_upwards [heq] with s hs
        simpa using hs
      · -- some coefficient is irrational: only finitely many integers survive
        push_neg at hrat
        refine thin_of_inter (T₀ := T) (thin_of_inter (T₀ := T') ?_)
        set S₂ : Set ℤ := {n : ℤ | n ∈ {n : ℤ | n ∈ S ∧ T < (n : ℝ)} ∧ T' < (n : ℝ)} with hS₂
        have hfin : S₂.Finite := by
          by_contra hinf
          rw [Set.not_finite] at hinf
          obtain ⟨u, husub, hucard⟩ := hinf.exists_subset_card_eq (D + 1)
          set e : Fin (D + 1) ↪o ℤ := u.orderEmbOfFin hucard with he
          have hemem : ∀ i, (e i : ℤ) ∈ S₂ := fun i =>
            husub (by rw [he]; exact u.orderEmbOfFin_mem hucard i)
          have hvinj : Function.Injective (fun i : Fin (D + 1) => ((e i : ℤ) : ℚ)) := by
            intro a b hab
            have hab' : ((e a : ℤ) : ℚ) = ((e b : ℤ) : ℚ) := hab
            exact e.injective (by exact_mod_cast hab')
          have hvals : ∀ i : Fin (D + 1), ∃ q : ℚ,
              p.eval (((e i : ℤ) : ℝ)) = (q : ℝ) := by
            intro i
            obtain ⟨hmem, hT'⟩ := hemem i
            obtain ⟨N, hN⟩ := hintval (e i) hmem
            refine ⟨(N : ℚ), ?_⟩
            rw [← hp _ hT', hN]
            simp
          choose r hr using hvals
          have hdegp : p.degree < ((Finset.univ : Finset (Fin (D + 1))).card : ℕ) := by
            have hcard : (Finset.univ : Finset (Fin (D + 1))).card = D + 1 := by simp
            rw [hcard]
            refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
            exact_mod_cast Nat.lt_succ_of_le hpdeg
          have hvinj' : Set.InjOn (fun i : Fin (D + 1) => algebraMap ℚ ℝ ((e i : ℤ) : ℚ))
              (Finset.univ : Finset (Fin (D + 1))) := by
            intro a _ b _ hab
            have hab' : (((e a : ℤ) : ℚ) : ℝ) = (((e b : ℤ) : ℚ) : ℝ) := by
              simpa [eq_ratCast (algebraMap ℚ ℝ)] using hab
            have : ((e a : ℤ) : ℚ) = ((e b : ℤ) : ℚ) := by exact_mod_cast hab'
            exact hvinj this
          have hmapeq := exists_map_eq_of_eval_mem_range (K := ℚ) (L := ℝ)
            (Finset.univ : Finset (Fin (D + 1))) (fun i => ((e i : ℤ) : ℚ)) hvinj' r hdegp
            (by
              intro i _
              rw [eq_ratCast (algebraMap ℚ ℝ), eq_ratCast (algebraMap ℚ ℝ)]
              exact hr i)
          obtain ⟨i, hi⟩ := hrat
          exact hi ((Lagrange.interpolate Finset.univ
            (fun i => ((e i : ℤ) : ℚ)) r).coeff i) (by rw [hmapeq, Polynomial.coeff_map]; simp)
        obtain ⟨B, hB⟩ := hfin.bddAbove
        refine thin_of_bddAbove (T := (B : ℝ)) ?_
        intro n hn
        exact_mod_cast hB hn
  · -- the imaginary part is eventually nonzero: no rational values far out
    rw [nhdsWithin, Filter.eventually_inf_principal] at hb
    obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp hb
    refine thin_of_bddAbove (T := max ρ⁻¹ 1) ?_
    intro n hn
    by_contra hcon
    push_neg at hcon
    have h1 : (1 : ℝ) < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hcon
    have hpos : (0 : ℝ) < (n : ℝ) := lt_trans zero_lt_one h1
    have h2 : ρ⁻¹ < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hcon
    have hx : ((n : ℝ))⁻¹ ≠ 0 := by positivity
    have hxr : |((n : ℝ))⁻¹| < ρ := by
      rw [abs_of_pos (by positivity)]
      exact inv_lt_of_inv_lt₀ hρ h2
    have hne : ψ ((n : ℝ))⁻¹ ≠ 0 := by
      refine hball ?_ ?_
      · rw [Real.dist_eq, sub_zero]; exact hxr
      · simpa using hx
    obtain ⟨c, hc⟩ := hn
    apply hne
    have : w (((s₀ : ℤ) : ℂ) + ((((n : ℝ))⁻¹ : ℝ) : ℂ)) = (c : ℂ) := by
      rw [hcastinv n hpos]; exact hc
    simp only [hψdef, this]
    simp

end GaloisForLFunctions.HTGeometry.HilbertIrreducibility
