import GaloisForLFunctions.HTGeometry.LagrangeNodeBounds
import GaloisForLFunctions.HTGeometry.SeparatedNodeInterpolantBound

/-!
# Anti-concentration of polynomials against block averages

A polynomial whose weighted average over each of `J` node blocks is small takes a small value
*inside* each block, by the intermediate value theorem applied to the average.  If the blocks lie
in separated intervals, the resulting `J` sample points are separated, and Lagrange interpolation
then forces every coefficient to be small.

This is the quantitative replacement for the compactness argument behind the invertibility of the
moment matrix of `J` measures carried by disjoint intervals.
-/

noncomputable section

open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- **A small weighted average forces a small value inside the node hull.** -/
theorem exists_small_value_in_hull {ι : Type*} [DecidableEq ι] {a b : ℝ} {S : Finset ι}
    (hS : S.Nonempty) {node : ι → ℝ} (hSmem : ∀ r ∈ S, node r ∈ Set.Icc a b)
    {w : ι → ℝ} (hw : ∀ r ∈ S, 0 < w r)
    {Q : ℝ → ℝ} (hQ : Continuous Q) {ε : ℝ}
    (hsmall : |∑ r ∈ S, w r * Q (node r)| ≤ ε * ∑ r ∈ S, w r) :
    ∃ s ∈ Set.Icc a b, |Q s| ≤ ε := by
  classical
  have hW : 0 < ∑ r ∈ S, w r := Finset.sum_pos hw hS
  set A : ℝ := (∑ r ∈ S, w r * Q (node r)) / (∑ r ∈ S, w r) with hAdef
  have hA : |A| ≤ ε := by
    rw [hAdef, abs_div, abs_of_pos hW, div_le_iff₀ hW]
    exact hsmall
  have hkey : ∑ r ∈ S, w r * Q (node r) = A * ∑ r ∈ S, w r := by
    rw [hAdef, div_mul_cancel₀ _ (ne_of_gt hW)]
  -- some node has value at most `A`, and some node has value at least `A`
  have hlow : ∃ r ∈ S, Q (node r) ≤ A := by
    by_contra hcon
    simp only [not_exists, not_and, not_le] at hcon
    have hlt : A * ∑ r ∈ S, w r < ∑ r ∈ S, w r * Q (node r) := by
      have hstep : ∀ r ∈ S, w r * A < w r * Q (node r) := fun r hr =>
        mul_lt_mul_of_pos_left (hcon r hr) (hw r hr)
      calc A * ∑ r ∈ S, w r = ∑ r ∈ S, w r * A := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun r _ => mul_comm A (w r)
        _ < ∑ r ∈ S, w r * Q (node r) := Finset.sum_lt_sum_of_nonempty hS hstep
    rw [hkey] at hlt
    exact lt_irrefl _ hlt
  have hhigh : ∃ r ∈ S, A ≤ Q (node r) := by
    by_contra hcon
    simp only [not_exists, not_and, not_le] at hcon
    have hlt : ∑ r ∈ S, w r * Q (node r) < A * ∑ r ∈ S, w r := by
      have hstep : ∀ r ∈ S, w r * Q (node r) < w r * A := fun r hr =>
        mul_lt_mul_of_pos_left (hcon r hr) (hw r hr)
      calc ∑ r ∈ S, w r * Q (node r) < ∑ r ∈ S, w r * A :=
            Finset.sum_lt_sum_of_nonempty hS hstep
        _ = A * ∑ r ∈ S, w r := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun r _ => mul_comm (w r) A
    rw [hkey] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨r₁, hr₁S, hr₁⟩ := hlow
  obtain ⟨r₂, hr₂S, hr₂⟩ := hhigh
  have hAmem : A ∈ Set.uIcc (Q (node r₁)) (Q (node r₂)) :=
    Set.mem_uIcc.mpr (Or.inl ⟨hr₁, hr₂⟩)
  have himg : Set.uIcc (Q (node r₁)) (Q (node r₂)) ⊆ Q '' Set.uIcc (node r₁) (node r₂) :=
    intermediate_value_uIcc hQ.continuousOn
  obtain ⟨s, hs, hsA⟩ := himg hAmem
  refine ⟨s, ?_, ?_⟩
  · have h1 := hSmem r₁ hr₁S
    have h2 := hSmem r₂ hr₂S
    have hsub := Set.uIcc_subset_uIcc (Set.mem_uIcc.mpr (Or.inl ⟨h1.1, h1.2⟩))
      (Set.mem_uIcc.mpr (Or.inl ⟨h2.1, h2.2⟩)) hs
    rwa [Set.uIcc_of_le (le_trans h1.1 h1.2)] at hsub
  · rw [hsA]
    exact hA

/-- **Real coefficient bound from smallness at nodes**, transported from the complex form. -/
theorem abs_coeff_le_of_nodes_real {J : ℕ} (s : Fin J → ℝ) (hs : Function.Injective s)
    (Q : Polynomial ℝ) (hdeg : Q.degree < (J : ℕ)) {ε : ℝ}
    (hsmall : ∀ i, |Q.eval (s i)| ≤ ε) (k : ℕ) :
    |Q.coeff k| ≤ ε * ∑ i : Fin J,
      ‖(∏ m ∈ Finset.univ.erase i,
          Lagrange.basisDivisor ((s i : ℂ)) ((s m : ℂ))).coeff k‖ := by
  classical
  set P : Polynomial ℂ := Q.map (algebraMap ℝ ℂ) with hPdef
  have hinjmap : Function.Injective (algebraMap ℝ ℂ) := by
    intro u v huv
    exact_mod_cast huv
  have hPdeg : P.degree < (J : ℕ) := by
    rw [hPdef, Polynomial.degree_map_eq_of_injective hinjmap]
    exact hdeg
  have hteval : ∀ i : Fin J, P.eval ((s i : ℂ)) = ((Q.eval (s i) : ℝ) : ℂ) := by
    intro i
    rw [hPdef, Polynomial.eval_map]
    have : ((s i : ℝ) : ℂ) = algebraMap ℝ ℂ (s i) := rfl
    rw [this, Polynomial.eval₂_at_apply]
    rfl
  have hPsmall : ∀ i : Fin J, ‖P.eval ((s i : ℂ))‖ ≤ ε := by
    intro i
    rw [hteval i, Complex.norm_real, Real.norm_eq_abs]
    exact hsmall i
  have htinj : Function.Injective (fun i : Fin J => ((s i : ℝ) : ℂ)) := by
    intro i j hij
    simp only [Complex.ofReal_inj] at hij
    exact hs hij
  have hcoeff : ‖P.coeff k‖ = |Q.coeff k| := by
    rw [hPdef, Polynomial.coeff_map]
    simp [Complex.norm_real, Real.norm_eq_abs]
  have := norm_coeff_le_of_nodes (fun i : Fin J => ((s i : ℝ) : ℂ)) htinj P hPdeg hPsmall k
  rwa [hcoeff] at this

/-- Fixed interpolation nodes in the unit interval. -/
def unitFixedNodes (J : ℕ) : Fin J → ℝ := fun i => (i : ℝ) / (J : ℝ)

theorem unitFixedNodes_injective {J : ℕ} : Function.Injective (unitFixedNodes J) := by
  intro i j hij
  rcases Nat.eq_zero_or_pos J with hJ | hJ
  · exact absurd i.isLt (by simp [hJ])
  have hJ0 : (0:ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have : (i : ℝ) = (j : ℝ) := by
    simp only [unitFixedNodes] at hij
    field_simp at hij
    exact hij
  exact Fin.ext (by exact_mod_cast this)

theorem unitFixedNodes_mem {J : ℕ} (i : Fin J) : unitFixedNodes J i ∈ Set.Icc (0:ℝ) 1 := by
  have hJ : 0 < J := i.pos
  have hJ0 : (0:ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have hile : (i : ℝ) ≤ (J : ℝ) := by
    have := i.isLt
    exact_mod_cast le_of_lt this
  constructor
  · rw [unitFixedNodes]
    positivity
  · rw [unitFixedNodes, div_le_one hJ0]
    exact hile

/-- The explicit constant converting a sup bound on the unit interval into a coefficient bound. -/
def unitCoeffConst (J k : ℕ) : ℝ :=
  ∑ i : Fin J, ‖(∏ m ∈ Finset.univ.erase i,
      Lagrange.basisDivisor ((unitFixedNodes J i : ℝ) : ℂ)
        ((unitFixedNodes J m : ℝ) : ℂ)).coeff k‖

theorem unitCoeffConst_nonneg (J k : ℕ) : 0 ≤ unitCoeffConst J k := by
  rw [unitCoeffConst]
  positivity

/-- **A sup bound on the unit interval bounds every coefficient.** -/
theorem abs_coeff_le_of_sup_unit {J : ℕ} (Q : Polynomial ℝ) (hdeg : Q.degree < (J : ℕ))
    {B : ℝ} (hB : ∀ x ∈ Set.Icc (0:ℝ) 1, |Q.eval x| ≤ B) (k : ℕ) :
    |Q.coeff k| ≤ B * unitCoeffConst J k :=
  abs_coeff_le_of_nodes_real (unitFixedNodes J) unitFixedNodes_injective Q hdeg
    (fun i => hB _ (unitFixedNodes_mem i)) k

/-- **Sup bound on the unit interval from smallness at separated nodes.** -/
theorem abs_eval_le_of_separated_nodes {J : ℕ} (hJ : 0 < J) {η : ℝ} (hη : 0 < η)
    (s : Fin J → ℝ) (hs : Function.Injective s)
    (hsmem : ∀ i, s i ∈ Set.Icc (0:ℝ) 1)
    (hsep : ∀ i k : Fin J, i ≠ k → η ≤ |s i - s k|)
    (Q : Polynomial ℝ) (hdeg : Q.degree < (J : ℕ)) {ε : ℝ}
    (hsmall : ∀ i, |Q.eval (s i)| ≤ ε) {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    |Q.eval x| ≤ ((J : ℝ)) * (2 ^ (J - 1) / (η ^ (J - 1) * ((J - 1).factorial))) * ε := by
  classical
  set T : Finset ℝ := Finset.image s Finset.univ with hTdef
  have hcardT : T.card = (J - 1) + 1 := by
    rw [hTdef, Finset.card_image_of_injective _ hs, Finset.card_univ, Fintype.card_fin]
    omega
  have hmemT : ∀ t ∈ T, ∃ i : Fin J, s i = t := by
    intro t ht
    rw [hTdef, Finset.mem_image] at ht
    obtain ⟨i, _, hi⟩ := ht
    exact ⟨i, hi⟩
  have hsep' : ∀ t ∈ T, ∀ u ∈ T, t ≠ u → η ≤ |t - u| := by
    intro t ht u hu htu
    obtain ⟨i, hi⟩ := hmemT t ht
    obtain ⟨k, hk⟩ := hmemT u hu
    have hik : i ≠ k := by
      intro h
      rw [h, hk] at hi
      exact htu hi.symm
    rw [← hi, ← hk]
    exact hsep i k hik
  have hclose : ∀ u ∈ T, |x - u| ≤ 1 := by
    intro u hu
    obtain ⟨i, hi⟩ := hmemT u hu
    have h1 := hsmem i
    rw [← hi]
    rw [abs_le]
    constructor <;> [linarith [hx.1, hx.2, h1.1, h1.2]; linarith [hx.1, hx.2, h1.1, h1.2]]
  have hB : ∀ t ∈ T, |Q.eval t| ≤ ε := by
    intro t ht
    obtain ⟨i, hi⟩ := hmemT t ht
    rw [← hi]
    exact hsmall i
  have hcardJ : T.card = J := by rw [hcardT]; omega
  have hdeg' : Q.degree < (T.card : ℕ) := by rw [hcardJ]; exact hdeg
  have hinjOn : Set.InjOn (id : ℝ → ℝ) (T : Set ℝ) := fun a _ b _ h => h
  have hQeq := Lagrange.eq_interpolate (v := (id : ℝ → ℝ)) hinjOn hdeg'
  have hfinal := HTGeometry.abs_eval_interpolate_le_of_separated (s := T) (N := J - 1)
    hcardT hη hsep' hclose (f := fun t => Q.eval t) (B := ε) hB
  have hQx : Q.eval x
      = (Lagrange.interpolate T (id : ℝ → ℝ) (fun t => Q.eval t)).eval x := by
    conv_lhs => rw [hQeq]
    rfl
  rw [hQx]
  have hJcast : ((J - 1 : ℕ) : ℝ) + 1 = (J : ℝ) := by
    have : (J - 1) + 1 = J := by omega
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) this
  calc |(Lagrange.interpolate T (id : ℝ → ℝ) (fun t => Q.eval t)).eval x|
      ≤ (((J - 1 : ℕ) : ℝ) + 1) * (2 ^ (J - 1) / (η ^ (J - 1) * ((J - 1).factorial))) * ε :=
        hfinal
    _ = ((J : ℝ)) * (2 ^ (J - 1) / (η ^ (J - 1) * ((J - 1).factorial))) * ε := by
        rw [hJcast]

/-! ### The polynomial with prescribed coefficients -/

/-- The real polynomial with prescribed coefficient vector. -/
def realCoeffPoly {J : ℕ} (c : Fin J → ℝ) : Polynomial ℝ :=
  ∑ k : Fin J, Polynomial.monomial (k : ℕ) (c k)

theorem realCoeffPoly_eval {J : ℕ} (c : Fin J → ℝ) (x : ℝ) :
    (realCoeffPoly c).eval x = ∑ k : Fin J, c k * x ^ (k : ℕ) := by
  rw [realCoeffPoly, Polynomial.eval_finsetSum]
  exact Finset.sum_congr rfl fun k _ => by rw [Polynomial.eval_monomial]

theorem realCoeffPoly_degree {J : ℕ} (c : Fin J → ℝ) :
    (realCoeffPoly c).degree < (J : ℕ) := by
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  refine (Finset.sup_lt_iff (by exact WithBot.bot_lt_coe _)).2 ?_
  intro k _
  refine lt_of_le_of_lt (Polynomial.degree_monomial_le _ _) ?_
  exact_mod_cast k.isLt

theorem realCoeffPoly_coeff {J : ℕ} (c : Fin J → ℝ) (k : Fin J) :
    (realCoeffPoly c).coeff (k : ℕ) = c k := by
  classical
  rw [realCoeffPoly, Polynomial.finsetSum_coeff, Finset.sum_eq_single k]
  · rw [Polynomial.coeff_monomial]
    simp
  · intro m _ hmk
    rw [Polynomial.coeff_monomial]
    have hne : (m : ℕ) ≠ (k : ℕ) := fun h => hmk (Fin.ext h)
    simp [hne]
  · intro h
    exact absurd (Finset.mem_univ k) h

/-! ### The anti-concentration bound -/

/-- **Block-average anti-concentration.**  A complex polynomial of degree below `J` whose weighted
average over each of `J` blocks — whose nodes lie in `η`-separated sub-intervals of the unit
interval — is at most `ε` has every coefficient bounded by an explicit multiple of `ε`. -/
theorem norm_le_of_block_averages {ι : Type*} [DecidableEq ι] {J : ℕ} (hJ : 0 < J) {η : ℝ}
    (hη : 0 < η) (a b : Fin J → ℝ)
    (hIcc : ∀ i : Fin J, ∀ t ∈ Set.Icc (a i) (b i), t ∈ Set.Icc (0:ℝ) 1)
    (hsep : ∀ i k : Fin J, i ≠ k → ∀ s ∈ Set.Icc (a i) (b i), ∀ u ∈ Set.Icc (a k) (b k),
      η ≤ |s - u|)
    (node weight : ι → ℝ)
    (S : Fin J → Finset ι) (hS : ∀ i, (S i).Nonempty)
    (hSmem : ∀ i : Fin J, ∀ r ∈ S i, node r ∈ Set.Icc (a i) (b i))
    (hw : ∀ i : Fin J, ∀ r ∈ S i, 0 < weight r)
    (v : Fin J → ℂ) {ε : ℝ}
    (havg : ∀ i : Fin J,
      ‖∑ r ∈ S i, (weight r : ℂ) * ∑ k : Fin J, v k * ((node r : ℝ) : ℂ) ^ (k : ℕ)‖
        ≤ ε * ∑ r ∈ S i, weight r) (k : Fin J) :
    ‖v k‖ ≤ 2 * (((J : ℝ)) * (2 ^ (J - 1) / (η ^ (J - 1) * ((J - 1).factorial)))
      * unitCoeffConst J (k : ℕ)) * ε := by
  classical
  set Kc : ℝ := ((J : ℝ)) * (2 ^ (J - 1) / (η ^ (J - 1) * ((J - 1).factorial))) with hKcdef
  set Qr : Polynomial ℝ := realCoeffPoly (fun k => (v k).re) with hQrdef
  set Qi : Polynomial ℝ := realCoeffPoly (fun k => (v k).im) with hQidef
  have hpowcast : ∀ (t : ℝ) (k : Fin J),
      ((t : ℝ) : ℂ) ^ (k : ℕ) = (((t ^ (k : ℕ) : ℝ)) : ℂ) := by
    intro t k
    push_cast
    ring
  have hsumre : ∀ i : Fin J,
      (∑ r ∈ S i, (weight r : ℂ) * ∑ k : Fin J, v k * ((node r : ℝ) : ℂ) ^ (k : ℕ)).re
        = ∑ r ∈ S i, weight r * Qr.eval (node r) := by
    intro i
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hinner : (∑ k : Fin J, v k * ((node r : ℝ) : ℂ) ^ (k : ℕ)).re
        = ∑ k : Fin J, (v k).re * (node r) ^ (k : ℕ) := by
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hpowcast, mul_comm, Complex.re_ofReal_mul, mul_comm]
    rw [Complex.re_ofReal_mul, hinner, hQrdef, realCoeffPoly_eval]
  have hsumim : ∀ i : Fin J,
      (∑ r ∈ S i, (weight r : ℂ) * ∑ k : Fin J, v k * ((node r : ℝ) : ℂ) ^ (k : ℕ)).im
        = ∑ r ∈ S i, weight r * Qi.eval (node r) := by
    intro i
    rw [Complex.im_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hinner : (∑ k : Fin J, v k * ((node r : ℝ) : ℂ) ^ (k : ℕ)).im
        = ∑ k : Fin J, (v k).im * (node r) ^ (k : ℕ) := by
      rw [Complex.im_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hpowcast, mul_comm, Complex.im_ofReal_mul, mul_comm]
    rw [Complex.im_ofReal_mul, hinner, hQidef, realCoeffPoly_eval]
  have hsample : ∀ (Q : Polynomial ℝ), Q.degree < (J : ℕ) →
      (∀ i : Fin J, |∑ r ∈ S i, weight r * Q.eval (node r)| ≤ ε * ∑ r ∈ S i, weight r) →
      ∀ x ∈ Set.Icc (0:ℝ) 1, |Q.eval x| ≤ Kc * ε := by
    intro Q hdegQ hQavg x hx
    have hchoice : ∀ i : Fin J, ∃ s ∈ Set.Icc (a i) (b i), |Q.eval s| ≤ ε := by
      intro i
      exact exists_small_value_in_hull (hS i) (hSmem i) (hw i)
        (Polynomial.continuous Q) (hQavg i)
    choose sr hsrmem hsrsmall using hchoice
    have hsrinj : Function.Injective sr := by
      intro i j hij
      by_contra hne
      have hsepij := hsep i j hne (sr i) (hsrmem i) (sr j) (hsrmem j)
      rw [hij, sub_self, abs_zero] at hsepij
      linarith
    have hsrunit : ∀ i, sr i ∈ Set.Icc (0:ℝ) 1 := fun i => hIcc i _ (hsrmem i)
    have hsrsep : ∀ i j : Fin J, i ≠ j → η ≤ |sr i - sr j| := fun i j hij =>
      hsep i j hij (sr i) (hsrmem i) (sr j) (hsrmem j)
    have hres := abs_eval_le_of_separated_nodes hJ hη sr hsrinj hsrunit hsrsep Q hdegQ
      hsrsmall hx
    rw [hKcdef]
    exact hres
  have hravg : ∀ i : Fin J,
      |∑ r ∈ S i, weight r * Qr.eval (node r)| ≤ ε * ∑ r ∈ S i, weight r := by
    intro i
    rw [← hsumre i]
    exact le_trans (Complex.abs_re_le_norm _) (havg i)
  have himavg : ∀ i : Fin J,
      |∑ r ∈ S i, weight r * Qi.eval (node r)| ≤ ε * ∑ r ∈ S i, weight r := by
    intro i
    rw [← hsumim i]
    exact le_trans (Complex.abs_im_le_norm _) (havg i)
  have hrsup := hsample Qr (by rw [hQrdef]; exact realCoeffPoly_degree _) hravg
  have hisup := hsample Qi (by rw [hQidef]; exact realCoeffPoly_degree _) himavg
  have hrcoeff : |(v k).re| ≤ (Kc * ε) * unitCoeffConst J (k : ℕ) := by
    have hc := abs_coeff_le_of_sup_unit Qr (by rw [hQrdef]; exact realCoeffPoly_degree _)
      hrsup (k : ℕ)
    rw [hQrdef, realCoeffPoly_coeff] at hc
    exact hc
  have hicoeff : |(v k).im| ≤ (Kc * ε) * unitCoeffConst J (k : ℕ) := by
    have hc := abs_coeff_le_of_sup_unit Qi (by rw [hQidef]; exact realCoeffPoly_degree _)
      hisup (k : ℕ)
    rw [hQidef, realCoeffPoly_coeff] at hc
    exact hc
  calc ‖v k‖ ≤ |(v k).re| + |(v k).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ (Kc * ε) * unitCoeffConst J (k : ℕ) + (Kc * ε) * unitCoeffConst J (k : ℕ) :=
        add_le_add hrcoeff hicoeff
    _ = 2 * (Kc * unitCoeffConst J (k : ℕ)) * ε := by ring

end GaloisForLFunctions.HTGeometry

end
