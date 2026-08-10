import GaloisForLFunctions.RHTower.BeurlingSystemZetaSeries
import GaloisForLFunctions.RHTower.BeurlingSystemTailBound

/-!
# The Mellin transform of the Möbius exponential sum

Termwise Mellin transformation turns the Möbius exponential sum of a Beurling system into its
Möbius Dirichlet series times the Gamma factor, which is `(BF16)`.  Absolute convergence of the
generalized-integer series on the half-plane to the right of one is what licenses the interchange.
-/

open scoped BigOperators
open Filter Topology

namespace RHTower

namespace BeurlingSystem

variable {B : BeurlingSystem}

/-- A discrete Beurling system has countably many generalized integers. -/
theorem countable_of_isDiscrete (hdisc : B.IsDiscrete) : Countable (Multiset B.Label) := by
  have hcover : (Set.univ : Set (Multiset B.Label))
      = ⋃ n : ℕ, {g : Multiset B.Label | B.intNorm g ≤ (n : ℝ)} := by
    ext g
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_setOf_eq, true_iff]
    exact ⟨⌈B.intNorm g⌉₊, Nat.le_ceil _⟩
  have hc : (Set.univ : Set (Multiset B.Label)).Countable := by
    rw [hcover]
    exact Set.countable_iUnion fun n => (hdisc (n : ℝ)).countable
  exact Set.countable_univ_iff.mp hc

/-- **The Mellin identity `(BF16)`.**  On the half-plane of absolute convergence the Mellin
transform of the Möbius exponential sum is the Gamma factor times the Möbius Dirichlet series. -/
theorem mellin_phi (hdisc : B.IsDiscrete) {C : ℝ} (hC : B.HasLinearCounting C) {s : ℂ}
    (hs : 1 < s.re) :
    mellin (fun x => ((B.phi x : ℝ) : ℂ)) s
      = Complex.Gamma s
        * ∑' g : Multiset B.Label, (B.moebius g : ℂ) / ((B.intNorm g : ℝ) : ℂ) ^ s := by
  haveI := countable_of_isDiscrete hdisc
  have hpos : ∀ g : Multiset B.Label, ((B.moebius g : ℂ)) = 0 ∨ 0 < B.intNorm g :=
    fun g => Or.inr (B.intNorm_pos g)
  have hsre : 0 < s.re := by linarith
  have hsumF : ∀ t ∈ Set.Ioi (0 : ℝ),
      HasSum (fun g : Multiset B.Label =>
        (B.moebius g : ℂ) * ((Real.exp (-B.intNorm g * t) : ℝ) : ℂ)) ((B.phi t : ℝ) : ℂ) := by
    intro t ht
    have ht0 : 0 < t := ht
    have hreal : HasSum (fun g : Multiset B.Label => B.gibbsTerm t g) (B.phi t) :=
      (summable_gibbsTerm hdisc hC ht0).hasSum
    have hcast : HasSum (fun g : Multiset B.Label => ((B.gibbsTerm t g : ℝ) : ℂ))
        ((B.phi t : ℝ) : ℂ) := Complex.ofRealCLM.hasSum hreal
    have hfun : (fun g : Multiset B.Label =>
        (B.moebius g : ℂ) * ((Real.exp (-B.intNorm g * t) : ℝ) : ℂ))
        = fun g => ((B.gibbsTerm t g : ℝ) : ℂ) := by
      funext g
      rw [gibbsTerm, show -B.intNorm g * t = -t * B.intNorm g from by ring]
      push_cast
      ring
    rw [hfun]
    exact hcast
  have hsummable : Summable fun g : Multiset B.Label =>
      ‖(B.moebius g : ℂ)‖ / (B.intNorm g) ^ s.re := by
    refine Summable.of_nonneg_of_le (fun g => ?_) (fun g => ?_)
      (summable_intNorm_rpow hdisc hC hs)
    · have hpow : (0 : ℝ) < (B.intNorm g) ^ s.re := Real.rpow_pos_of_pos (B.intNorm_pos g) _
      exact div_nonneg (norm_nonneg _) hpow.le
    · have hnorm : ‖(B.moebius g : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast abs_moebius_le_one (B := B) g
      have hpow : (0 : ℝ) < (B.intNorm g) ^ s.re := Real.rpow_pos_of_pos (B.intNorm_pos g) _
      rw [div_le_iff₀ hpow, Real.rpow_neg (B.intNorm_pos g).le, inv_mul_cancel₀ (ne_of_gt hpow)]
      exact hnorm
  have hmain := hasSum_mellin hpos hsre hsumF hsummable
  rw [← hmain.tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun g => ?_
  rw [mul_div_assoc]


/-! ## The complex Dirichlet series and the inversion -/

variable (B) in
/-- The complex zeta series of a Beurling system. -/
noncomputable def zetaSeriesC (s : ℂ) : ℂ :=
  ∑' g : Multiset B.Label, ((B.intNorm g : ℝ) : ℂ) ^ (-s)

variable (B) in
/-- The complex Möbius Dirichlet series. -/
noncomputable def moebiusSeriesC (s : ℂ) : ℂ :=
  ∑' g : Multiset B.Label, (B.moebius g : ℂ) * ((B.intNorm g : ℝ) : ℂ) ^ (-s)

theorem norm_intNorm_cpow (g : Multiset B.Label) (s : ℂ) :
    ‖((B.intNorm g : ℝ) : ℂ) ^ (-s)‖ = (B.intNorm g) ^ (-s.re) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (B.intNorm_pos g), Complex.neg_re]

theorem summable_intNorm_cpow (hdisc : B.IsDiscrete) {C : ℝ} (hC : B.HasLinearCounting C)
    {s : ℂ} (hs : 1 < s.re) :
    Summable fun g : Multiset B.Label => ((B.intNorm g : ℝ) : ℂ) ^ (-s) := by
  refine Summable.of_norm ?_
  refine (summable_intNorm_rpow hdisc hC hs).congr fun g => ?_
  rw [norm_intNorm_cpow]

theorem summable_moebius_cpow (hdisc : B.IsDiscrete) {C : ℝ} (hC : B.HasLinearCounting C)
    {s : ℂ} (hs : 1 < s.re) :
    Summable fun g : Multiset B.Label =>
      (B.moebius g : ℂ) * ((B.intNorm g : ℝ) : ℂ) ^ (-s) := by
  refine Summable.of_norm_bounded (summable_intNorm_rpow hdisc hC hs) fun g => ?_
  rw [norm_mul, norm_intNorm_cpow]
  have hnorm : ‖(B.moebius g : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast abs_moebius_le_one (B := B) g
  have hpos : (0 : ℝ) < (B.intNorm g) ^ (-s.re) := Real.rpow_pos_of_pos (B.intNorm_pos g) _
  nlinarith

/-- **The complex Dirichlet inversion.**  On the half-plane of absolute convergence the Möbius
Dirichlet series is the reciprocal of the zeta series. -/
theorem moebiusSeriesC_mul_zetaSeriesC (hdisc : B.IsDiscrete) {C : ℝ}
    (hC : B.HasLinearCounting C) {s : ℂ} (hs : 1 < s.re) :
    B.moebiusSeriesC s * B.zetaSeriesC s = 1 := by
  classical
  haveI := countable_of_isDiscrete hdisc
  set F : (Multiset B.Label) × (Multiset B.Label) → ℂ := fun p =>
    ((B.moebius p.1 : ℂ) * ((B.intNorm p.1 : ℝ) : ℂ) ^ (-s))
      * (((B.intNorm p.2 : ℝ) : ℂ) ^ (-s)) with hF
  have hZ := summable_intNorm_cpow hdisc hC hs
  have hM := summable_moebius_cpow hdisc hC hs
  have hZr := summable_intNorm_rpow hdisc hC hs
  have hprod : Summable fun p : (Multiset B.Label) × (Multiset B.Label) =>
      (B.intNorm p.1) ^ (-s.re) * (B.intNorm p.2) ^ (-s.re) :=
    hZr.mul_of_nonneg hZr (fun g => Real.rpow_nonneg (B.intNorm_pos g).le _)
      (fun g => Real.rpow_nonneg (B.intNorm_pos g).le _)
  have hFsum : Summable F := by
    refine Summable.of_norm_bounded hprod fun p => ?_
    have hnorm : ‖(B.moebius p.1 : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast abs_moebius_le_one (B := B) p.1
    have h1 : (0 : ℝ) < (B.intNorm p.1) ^ (-s.re) := Real.rpow_pos_of_pos (B.intNorm_pos _) _
    have h2 : (0 : ℝ) < (B.intNorm p.2) ^ (-s.re) := Real.rpow_pos_of_pos (B.intNorm_pos _) _
    rw [hF]
    simp only [norm_mul, norm_intNorm_cpow]
    calc ‖(B.moebius p.1 : ℂ)‖ * (B.intNorm p.1) ^ (-s.re) * (B.intNorm p.2) ^ (-s.re)
        ≤ 1 * (B.intNorm p.1) ^ (-s.re) * (B.intNorm p.2) ^ (-s.re) := by gcongr
      _ = (B.intNorm p.1) ^ (-s.re) * (B.intNorm p.2) ^ (-s.re) := by ring
  have hpairsum : B.moebiusSeriesC s * B.zetaSeriesC s = ∑' p, F p := by
    rw [moebiusSeriesC, zetaSeriesC, hF]
    exact hM.tsum_mul_tsum hZ hFsum
  rw [hpairsum]
  set e := Equiv.sigmaFiberEquiv fun p : (Multiset B.Label) × (Multiset B.Label) => p.1 + p.2
    with he
  have hsigma : Summable (F ∘ e) := (e.summable_iff).mpr hFsum
  have hregroup : ∑' p, F p = ∑' n : Multiset B.Label,
      ∑' c : {p : (Multiset B.Label) × (Multiset B.Label) // p.1 + p.2 = n},
        F (c : (Multiset B.Label) × (Multiset B.Label)) := by
    have h1 : ∑' p, F p
        = ∑' x : (Σ n : Multiset B.Label,
            {p : (Multiset B.Label) × (Multiset B.Label) // p.1 + p.2 = n}), (F ∘ e) x :=
      (e.tsum_eq F).symm
    rw [h1, hsigma.tsum_sigma]
    rfl
  rw [hregroup]
  have hfibre : ∀ n : Multiset B.Label,
      (∑' c : {p : (Multiset B.Label) × (Multiset B.Label) // p.1 + p.2 = n},
        F (c : (Multiset B.Label) × (Multiset B.Label)))
        = (if n = 0 then (1 : ℂ) else 0) := by
    intro n
    letI : Fintype {p : (Multiset B.Label) × (Multiset B.Label) // p.1 + p.2 = n} :=
      Fintype.ofEquiv _ (divisorPairEquiv n).symm
    rw [tsum_fintype]
    have hval : ∀ c : {p : (Multiset B.Label) × (Multiset B.Label) // p.1 + p.2 = n},
        F (c : (Multiset B.Label) × (Multiset B.Label))
          = (B.moebius ((c : (Multiset B.Label) × (Multiset B.Label)).1) : ℂ)
            * ((B.intNorm n : ℝ) : ℂ) ^ (-s) := by
      rintro ⟨⟨d, g⟩, hdg⟩
      have hnorm : ((B.intNorm d : ℝ) : ℂ) * ((B.intNorm g : ℝ) : ℂ) = ((B.intNorm n : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul, ← intNorm_add, hdg]
      rw [hF]
      simp only
      rw [mul_assoc, ← Complex.mul_cpow_ofReal_nonneg (B.intNorm_pos d).le (B.intNorm_pos g).le,
        ← Complex.ofReal_mul, ← intNorm_add, hdg]
    rw [Finset.sum_congr rfl fun c _ => hval c, ← Finset.sum_mul]
    have hsum : ∑ c : {p : (Multiset B.Label) × (Multiset B.Label) // p.1 + p.2 = n},
        (B.moebius ((c : (Multiset B.Label) × (Multiset B.Label)).1) : ℂ)
        = ((∑ d ∈ n.powerset.toFinset, B.moebius d : ℤ) : ℂ) := by
      push_cast
      rw [← Finset.sum_coe_sort n.powerset.toFinset (fun d => (B.moebius d : ℂ))]
      refine Fintype.sum_equiv (divisorPairEquiv n)
        (fun c => (B.moebius ((c : (Multiset B.Label) × (Multiset B.Label)).1) : ℂ))
        (fun d => (B.moebius (d : Multiset B.Label) : ℂ)) ?_
      intro c
      rfl
    rw [hsum, B.sum_moebius_divisors n]
    by_cases hn : n = 0
    · rw [if_pos hn, if_pos hn, hn, intNorm_zero]
      norm_num
    · rw [if_neg hn, if_neg hn]
      norm_num
  rw [tsum_congr hfibre, tsum_eq_single 0]
  · rw [if_pos rfl]
  · intro n hn
    rw [if_neg hn]

theorem zetaSeriesC_ne_zero (hdisc : B.IsDiscrete) {C : ℝ} (hC : B.HasLinearCounting C)
    {s : ℂ} (hs : 1 < s.re) : B.zetaSeriesC s ≠ 0 := by
  intro hzero
  have := moebiusSeriesC_mul_zetaSeriesC hdisc hC hs
  rw [hzero, mul_zero] at this
  exact zero_ne_one this

/-- **The Mellin identity in the form `(BF16)`.**  On the half-plane of absolute convergence the
Mellin transform of the Möbius exponential sum is `Γ(s)/ζ_P(s)`. -/
theorem mellin_phi_eq_gamma_div (hdisc : B.IsDiscrete) {C : ℝ} (hC : B.HasLinearCounting C)
    {s : ℂ} (hs : 1 < s.re) :
    mellin (fun x => ((B.phi x : ℝ) : ℂ)) s = Complex.Gamma s / B.zetaSeriesC s := by
  have hzero := zetaSeriesC_ne_zero hdisc hC hs
  have hinv := moebiusSeriesC_mul_zetaSeriesC hdisc hC hs
  have hM : B.moebiusSeriesC s = (B.zetaSeriesC s)⁻¹ := by
    field_simp at hinv ⊢
    linear_combination hinv
  rw [mellin_phi hdisc hC hs]
  have hterm : ∀ g : Multiset B.Label,
      (B.moebius g : ℂ) / ((B.intNorm g : ℝ) : ℂ) ^ s
        = (B.moebius g : ℂ) * ((B.intNorm g : ℝ) : ℂ) ^ (-s) := by
    intro g
    rw [Complex.cpow_neg, div_eq_mul_inv]
  rw [tsum_congr hterm, ← moebiusSeriesC, hM, div_eq_mul_inv]


/-! ## Analytic behaviour of the Möbius exponential sum -/

theorem continuousOn_phi (hdisc : B.IsDiscrete) {C : ℝ} (hC : B.HasLinearCounting C) {a : ℝ}
    (ha : 0 < a) : ContinuousOn (fun x => B.phi x) (Set.Ici a) := by
  refine continuousOn_tsum (fun g => ?_) (summable_expNegNorm hdisc hC ha) ?_
  · have hcont : Continuous fun x : ℝ => B.gibbsTerm x g := by
      unfold gibbsTerm
      fun_prop
    exact hcont.continuousOn
  · intro g x hx
    have hax : a ≤ x := hx
    rw [gibbsTerm, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have h1 := abs_moebius_le_one (B := B) g
    have h2 : Real.exp (-x * B.intNorm g) ≤ Real.exp (-a * B.intNorm g) := by
      refine Real.exp_le_exp.mpr ?_
      have hg : 1 ≤ B.intNorm g := B.one_le_intNorm g
      nlinarith
    have h3 : (0 : ℝ) < Real.exp (-x * B.intNorm g) := Real.exp_pos _
    nlinarith

theorem continuousOn_phi_Ioi (hdisc : B.IsDiscrete) {C : ℝ} (hC : B.HasLinearCounting C) :
    ContinuousOn (fun x => B.phi x) (Set.Ioi 0) := by
  intro x hx
  have hx0 : 0 < x := hx
  have hcont := continuousOn_phi hdisc hC (a := x / 2) (by linarith)
  have hmem : Set.Ici (x / 2) ∈ nhds x :=
    Filter.mem_of_superset (isOpen_Ioi.mem_nhds (show x / 2 < x by linarith))
      fun y hy => le_of_lt (Set.mem_Ioi.mp hy)
  exact (hcont.continuousAt hmem).continuousWithinAt

theorem abs_phi_le (hdisc : B.IsDiscrete) {C : ℝ} (hC : B.HasLinearCounting C) {x : ℝ}
    (hx : 1 ≤ x) :
    |B.phi x| ≤ Real.exp (-x / 2) * ∑' g : Multiset B.Label, Real.exp (-(1 / 2 : ℝ) * B.intNorm g) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hsum := summable_expNegNorm hdisc hC hhalf
  have hbound : ∀ g : Multiset B.Label,
      ‖B.gibbsTerm x g‖ ≤ Real.exp (-x / 2) * Real.exp (-(1 / 2 : ℝ) * B.intNorm g) := by
    intro g
    have hg : 1 ≤ B.intNorm g := B.one_le_intNorm g
    have hstep : Real.exp (-x * B.intNorm g)
        ≤ Real.exp (-x / 2) * Real.exp (-(1 / 2 : ℝ) * B.intNorm g) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      nlinarith
    have h1 := norm_gibbsTerm_le (B := B) x g
    linarith
  have hsummable : Summable fun g : Multiset B.Label =>
      Real.exp (-x / 2) * Real.exp (-(1 / 2 : ℝ) * B.intNorm g) := hsum.mul_left _
  calc |B.phi x| = ‖∑' g : Multiset B.Label, B.gibbsTerm x g‖ := by
        rw [phi, Real.norm_eq_abs]
    _ ≤ ∑' g : Multiset B.Label,
          Real.exp (-x / 2) * Real.exp (-(1 / 2 : ℝ) * B.intNorm g) := by
        refine norm_tsum_le_tsum_norm ?_ |>.trans ?_
        · exact Summable.of_norm_bounded hsummable fun g => by
            rw [norm_norm]; exact hbound g
        · exact Summable.tsum_le_tsum hbound
            (Summable.of_norm_bounded hsummable fun g => by rw [norm_norm]; exact hbound g)
            hsummable
    _ = Real.exp (-x / 2) * ∑' g : Multiset B.Label,
          Real.exp (-(1 / 2 : ℝ) * B.intNorm g) := tsum_mul_left


/-! ## The strict-half failure -/

/-- **The strict-half failure `(BF13)`.**  If the continued zeta function of the system vanishes at
a point strictly to the right of the decay exponent, the Möbius exponential sum cannot decay at
that rate as `x ↓ 0`. -/
theorem not_isBigO_rpow_of_continuation_eq_zero (hdisc : B.IsDiscrete) {C : ℝ}
    (hC : B.HasLinearCounting C) {Z : ℂ → ℂ} {a : ℝ} {ρ : ℂ}
    (hZ : AnalyticOnNhd ℂ Z {s : ℂ | a < s.re})
    (hagree : ∀ s : ℂ, 1 < s.re → Z s = B.zetaSeriesC s)
    (ha : 0 < a) (ha1 : a < 1) (hρ : a < ρ.re) (hρ0 : Z ρ = 0) :
    ¬ ((fun x : ℝ => ((B.phi x : ℝ) : ℂ)) =O[nhdsWithin 0 (Set.Ioi 0)]
        fun x : ℝ => x ^ (-a)) := by
  intro hO
  classical
  set Φ : ℝ → ℂ := fun x => ((B.phi x : ℝ) : ℂ) with hΦ
  have hloc : MeasureTheory.LocallyIntegrableOn Φ (Set.Ioi 0) := by
    refine ContinuousOn.locallyIntegrableOn ?_ measurableSet_Ioi
    exact Complex.continuous_ofReal.comp_continuousOn (continuousOn_phi_Ioi hdisc hC)
  set S : ℝ := ∑' g : Multiset B.Label, Real.exp (-(1 / 2 : ℝ) * B.intNorm g) with hS
  have hdecay : ∀ c : ℝ, Φ =O[Filter.atTop] fun x : ℝ => x ^ (-c) := by
    intro c
    have hexp := isLittleO_exp_neg_mul_rpow_atTop (a := (1 / 2 : ℝ)) (by norm_num) (-c)
    refine Asymptotics.IsBigO.trans ?_ hexp.isBigO
    refine Asymptotics.IsBigO.of_bound S ?_
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
    have hbnd := abs_phi_le hdisc hC hx
    have hSnn : 0 ≤ S := by
      rw [hS]
      exact tsum_nonneg fun g => (Real.exp_pos _).le
    rw [hΦ, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have hrw : Real.exp (-(1 / 2 : ℝ) * x) = Real.exp (-x / 2) := by
      congr 1
      ring
    rw [hrw]
    calc |B.phi x| ≤ Real.exp (-x / 2) * S := hbnd
      _ = S * Real.exp (-x / 2) := by ring
  have hdiff : ∀ s : ℂ, a < s.re → DifferentiableAt ℂ (mellin Φ) s := by
    intro s hs
    exact mellin_differentiableAt_of_isBigO_rpow hloc (hdecay (s.re + 1)) (by linarith) hO hs
  set U : Set ℂ := {s : ℂ | a < s.re} with hU
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUconv : Convex ℝ U := by
    rw [hU]
    exact convex_halfSpace_gt (by
      exact ⟨fun x y => by simp [Complex.add_re], fun c x => by simp⟩) a
  have hMdiffOn : DifferentiableOn ℂ (mellin Φ) U :=
    fun s hs => (hdiff s hs).differentiableWithinAt
  have hManalytic : AnalyticOnNhd ℂ (mellin Φ) U := hMdiffOn.analyticOnNhd hUopen
  have hGammaNe : ∀ s ∈ U, ∀ m : ℕ, s ≠ -(m : ℂ) := by
    intro s hs m hcon
    have hre : a < s.re := hs
    rw [hcon] at hre
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hGammaDiffOn : DifferentiableOn ℂ Complex.Gamma U :=
    fun s hs => (Complex.differentiableAt_Gamma s (hGammaNe s hs)).differentiableWithinAt
  have hGammaAnalytic : AnalyticOnNhd ℂ Complex.Gamma U := hGammaDiffOn.analyticOnNhd hUopen
  set G : ℂ → ℂ := fun s => mellin Φ s * Z s with hG
  have hGanalytic : AnalyticOnNhd ℂ G U := hManalytic.mul hZ
  have hEq1 : Set.EqOn G Complex.Gamma {s : ℂ | 1 < s.re} := by
    intro s hs
    have hs1 : 1 < s.re := hs
    have hne := zetaSeriesC_ne_zero hdisc hC hs1
    rw [hG]
    simp only
    rw [hΦ, mellin_phi_eq_gamma_div hdisc hC hs1, hagree s hs1, div_mul_cancel₀ _ hne]
  have hopen1 : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem2 : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by
    simp only [Set.mem_setOf_eq]
    norm_num
  have hev : G =ᶠ[nhds (2 : ℂ)] Complex.Gamma :=
    Filter.eventuallyEq_of_mem (hopen1.mem_nhds hmem2) hEq1
  have h2U : (2 : ℂ) ∈ U := by
    rw [hU]
    simp only [Set.mem_setOf_eq]
    norm_num
    linarith
  have hEq := hGanalytic.eqOn_of_preconnected_of_eventuallyEq hGammaAnalytic
    hUconv.isPreconnected h2U hev
  have hρU : ρ ∈ U := hρ
  have hfinal := hEq hρU
  rw [hG] at hfinal
  simp only [hρ0, mul_zero] at hfinal
  exact Complex.Gamma_ne_zero (hGammaNe ρ hρU) hfinal.symm


/-- **The aperture form of the strict-half failure `(BF14)`.**  On any schedule satisfying the seam
condition `(BF5)`, a strict-half decay bound for the zero/one-large-prime difference would force one
for the whole Möbius exponential sum, which the continuation forbids. -/
theorem not_aperture_decay_of_continuation_eq_zero (hdisc : B.IsDiscrete) {C' : ℝ}
    (hC' : B.HasLinearCounting C') {κ C θ : ℝ} (hN : B.HasCountingError κ C θ) (hκ : 0 ≤ κ)
    (hC0 : 0 ≤ C) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    {Z : ℂ → ℂ} {a : ℝ} {ρ : ℂ}
    (hZ : AnalyticOnNhd ℂ Z {s : ℂ | a < s.re})
    (hagree : ∀ s : ℂ, 1 < s.re → Z s = B.zetaSeriesC s)
    (ha12 : 1 / 2 < a) (ha1 : a < 1) (hρ : a < ρ.re) (hρ0 : Z ρ = 0)
    {z : ℝ → ℝ} {K₀ x₀ : ℝ} (hx₀ : 0 < x₀)
    (hz : ∀ x : ℝ, 0 < x → x ≤ x₀ → 1 ≤ z x)
    (hBF5 : ∀ x : ℝ, 0 < x → x ≤ x₀ → (1 : ℝ) / 2 * Real.log (1 / x) ≤ x * (z x) ^ 2)
    (hbracket : ∀ x : ℝ, 0 < x → x ≤ x₀ →
      |B.apertureSum (z x) x
          - ∑' p : {p : B.Label // z x < B.labelNorm p},
              B.apertureSum (z x) (B.labelNorm (p : B.Label) * x)| ≤ K₀ * x ^ (-a)) :
    False := by
  have ha0 : 0 < a := by linarith
  refine not_isBigO_rpow_of_continuation_eq_zero hdisc hC' hZ hagree ha0 ha1 hρ hρ0 ?_
  obtain ⟨K, hKpos, hKmem⟩ :
      ∃ K : ℝ, 0 < K ∧ ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ∀ w : ℝ, 1 ≤ w → (1 : ℝ) / 2 * Real.log (1 / x) ≤ x * w ^ 2 →
          |B.higherLargeSum w x| ≤ K * x ^ (-((1 : ℝ) / 2)) := by
    refine ⟨|κ * expGeomSum + 2 * C * expGeomLinSum + 1| + 1, by positivity, ?_⟩
    filter_upwards [eventually_abs_higherLargeSum_le hdisc hN hC' hκ hC0 hθ0 hθ1,
      self_mem_nhdsWithin] with x hx hxpos w hw hseam
    have hxx : (0 : ℝ) < x := hxpos
    have hbound := hx w hw hseam
    have hpow : (0 : ℝ) < x ^ (-((1 : ℝ) / 2)) := Real.rpow_pos_of_pos hxx _
    have hle : κ * expGeomSum + 2 * C * expGeomLinSum + 1
        ≤ |κ * expGeomSum + 2 * C * expGeomLinSum + 1| + 1 := by
      have := le_abs_self (κ * expGeomSum + 2 * C * expGeomLinSum + 1)
      linarith
    calc |B.higherLargeSum w x|
        ≤ (κ * expGeomSum + 2 * C * expGeomLinSum + 1) * x ^ (-((1 : ℝ) / 2)) := hbound
      _ ≤ (|κ * expGeomSum + 2 * C * expGeomLinSum + 1| + 1) * x ^ (-((1 : ℝ) / 2)) := by
          exact mul_le_mul_of_nonneg_right hle hpow.le
  refine Asymptotics.IsBigO.of_bound (|K₀| + K) ?_
  filter_upwards [hKmem, self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds (eventually_le_nhds (by linarith : (0:ℝ) < x₀)),
    eventually_nhdsWithin_of_eventually_nhds (eventually_le_nhds (by norm_num : (0:ℝ) < 1))]
    with x hxK hxpos hxx₀ hx1
  have hxx : (0 : ℝ) < x := hxpos
  have hsplit := phi_eq_apertureSum_sub_tsum_add hdisc hC' hxx (z x)
  have hbr := hbracket x hxx hxx₀
  have hrem := hxK (z x) (hz x hxx hxx₀) (hBF5 x hxx hxx₀)
  have hpowa : (0 : ℝ) < x ^ (-a) := Real.rpow_pos_of_pos hxx _
  have hcompare : x ^ (-((1 : ℝ) / 2)) ≤ x ^ (-a) :=
    Real.rpow_le_rpow_of_exponent_ge hxx hx1 (by linarith)
  have habs : |B.phi x| ≤ (|K₀| + K) * x ^ (-a) := by
    have htri : |B.phi x|
        ≤ |B.apertureSum (z x) x
            - ∑' p : {p : B.Label // z x < B.labelNorm p},
                B.apertureSum (z x) (B.labelNorm (p : B.Label) * x)|
          + |B.higherLargeSum (z x) x| := by
      rw [hsplit]
      exact abs_add_le _ _
    have hK₀ : K₀ * x ^ (-a) ≤ |K₀| * x ^ (-a) :=
      mul_le_mul_of_nonneg_right (le_abs_self K₀) hpowa.le
    have hKle : K * x ^ (-((1 : ℝ) / 2)) ≤ K * x ^ (-a) :=
      mul_le_mul_of_nonneg_left hcompare hKpos.le
    calc |B.phi x| ≤ K₀ * x ^ (-a) + K * x ^ (-((1 : ℝ) / 2)) := by linarith
      _ ≤ |K₀| * x ^ (-a) + K * x ^ (-a) := by linarith
      _ = (|K₀| + K) * x ^ (-a) := by ring
  rw [Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpowa]
  exact habs

end BeurlingSystem

end RHTower
